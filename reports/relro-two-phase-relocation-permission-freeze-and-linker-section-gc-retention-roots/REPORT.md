# RELRO two-phase relocation, permission freeze, and linker section GC retention roots (`Toy.RelroGc`)

Lean `leanprover/lean4:v4.34.1`, core Lean only (no Mathlib, no `Std` import). Lake project in `lean/` (one library, `ToyRelroGc`; every declaration lives in the namespace `Toy.RelroGc`). Every Lean statement below is quoted verbatim from the sources with a `file:line` citation, and proofs are elided. Every quoted theorem is kernel-checked with standard axioms only; the record is under Evidence.

## Summary

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler. Every connection to a real system is labelled `derived (modeling bridge)` and rests on the quoted documentation or source, not on the Lean proofs.

The package has two separate toy models: a loader model for RELRO (results R1–R5c: two-phase relocate-then-protect loading, placement of relocated constants, eager versus lazy binding, page rounding of the protected range, relocation order) and a section-GC model for linkers (results R6a–R8b: soundness of reachability-based retention, start/stop registries, compiler-then-linker retention). No interaction between the two models is proved.

One statement per result, each stating its hypotheses (identical to the plain claim of its card under Findings):

* **R1.** For every loader input c, symbol table sa, program ops and protect position k, consider the timeline produced by `timeline c ops k` (the relocations of c in list order, then the program operations ops, with one protect event inserted at position k). If (H1) every relocated slot is mapped writable, (H2) k = c.relocs.length (protect right after the last relocation and before the first program operation), (H3) protect covers every RELRO byte, and (H4) protect covers no mutable byte, then no relocation faults, the memory at protect equals the fully relocated image applyAll sa c.relocs c.init, every program write to a RELRO byte faults, and every program write to a mutable byte succeeds.
* **R2a.** If a dynamic relocation r of loader input c (r ∈ c.relocs, that is, r is applied by the loader at load time) writes a byte of kind ro (.rodata), then for every symbol table sa and program ops the two-phase load of c faults.
* **R2d.** Let r be a dynamic relocation of loader input c (r ∈ c.relocs) such that every other relocation of c whose slot differs from r's writes a mapped-writable slot, and let protect cover every RELRO byte (H3) and no mutable byte (H4). Then, for every symbol table sa, the two-phase load succeeds and r's slot has post-entry write protection iff r's slot is a RELRO byte.
* **R3a.** For every loader input c (any layout, any protected range), symbol table sa, and slot x lazily bound to symbol t (x is listed as lazy with target t, initially holds the resolver stub, and no dynamic relocation writes it), it is not the case that both the call through x works (CallWorks: the one-operation program [call x], run as the sole program operation immediately after entry, loads without fault and jumps to t's address) and x has post-entry write protection.
* **R3b.** For every loader input c, symbol table sa and list B of bindings (x, t): if every binding in B is either eagerly bound with x a RELRO byte or lazily bound (with x anywhere), the call through every binding slot in B works (CallWorks c sa x t: the one-operation program [call x], run as the sole program operation immediately after entry, loads without fault and jumps to t's address), and protect covers every RELRO byte (H3), then every binding slot in B has post-entry write protection iff every binding in B is eagerly bound.
* **R3c.** For every loader input c, symbol table sa and list B of bindings (x, t): if every binding in B is eagerly bound with x a RELRO byte or lazily bound with x a mutable byte, every relocated slot is mapped writable (H1), and protect covers no mutable byte (H4), then for every binding (x, t) in B the one-operation program [call x], run as the sole program operation immediately after entry, loads without fault and jumps to t's address (CallWorks).
* **R4a.** For every page size P and layout L, if the RELRO bytes of L are exactly the range [rs, re) (rs ≤ re ≤ L.length) and no mutable byte lies in [alignDown P rs, rs) (the bytes of the page of address rs below rs, where alignDown P a = a / P * P uses floor division; for P > 0 this range is empty when rs % P = 0, for P = 0 it is [0, rs) because floor division by zero gives alignDown 0 rs = 0, and it is defined also for an empty RELRO range rs = re), then the down-down mask [alignDown P rs, alignDown P re) covers no mutable byte.
* **R4b.** For every page size P and layout L, if the RELRO bytes of L are exactly the non-empty range [rs, re) (rs < re), then the down-down mask [alignDown P rs, alignDown P re) (ends rounded down by floor division) covers every RELRO byte iff re % P = 0 (Nat modulo, with re % 0 = re; for P = 0 both sides are false).
* **R4c.** For every page size P > 0 and layout L, if the RELRO bytes of L are exactly [rs, re), then the down-up mask covers every RELRO byte. For rs < re the down-up mask is [alignDown P rs, alignUp P re), with alignUp P a = (a + P - 1) / P * P (floor division and truncated subtraction); for rs = re there is no RELRO byte and the mask is empty (roundedMask guards the empty range).
* **R4d.** For every page size P > 0 and layout L, if the RELRO bytes of L are exactly the non-empty range [rs, re) (rs < re), then the down-up mask [alignDown P rs, alignUp P re) covers no mutable byte iff no mutable byte lies in [alignDown P rs, rs) and none lies in [re, alignUp P re) (alignDown P a = a / P * P and alignUp P a = (a + P - 1) / P * P, by floor division and truncated subtraction).
* **R4e.** For every layout L and page size P (pages are the classes of equal floor quotient a / P; for P = 0 every address is on page 0), some page-granular mask covers every RELRO byte and no mutable byte iff no page holds both a RELRO byte and a mutable byte.
* **R4g.** For every page size P > 0 and layout L whose RELRO bytes are exactly the non-empty range [rs, re) (rs < re): some page-granular mask covers every RELRO byte and no mutable byte iff no mutable byte lies in [alignDown P rs, rs) and none lies in [re, alignUp P re) (alignDown and alignUp by floor division and truncated subtraction). When re % P = 0 the second range is empty (alignUp_eq_self_of_mod_eq_zero).
* **R5a.** For every symbol table sa and initial memory m: if every relocation in rs is address-only (its value depends on symbol addresses alone) and the relocations of rs write pairwise distinct slots, then for every order rs' that is a permutation of rs, applying rs' gives the same image as applying rs.
* **R5c.** For every symbol table sa and initial memory m: let A be address-only relocations with pairwise distinct slots, and R resolver relocations with pairwise distinct slots, each of which reads memory only at addresses that no relocation of R writes (it may read any slot of A that no relocation of R writes, and any other memory not written by R). Then for every order produced by permuting A to A' and R to R' and applying all of A' before any of R' (A' ++ R'), the image equals that of A ++ R.
* **R6a.** For every GC input g, start/stop policy pol and run (a list of section accesses, each an edge access, a bounds access or an implicit access): if (A1) every edge access edge i j follows a relocation edge (i, j) ∈ g.edges from a section i that is a root or was reached by an earlier access of the run, (A2) every implicit access reaches a root, and (A3) every bounds access bounds i X j comes from a section i that references the bounds of X ((i, X) ∈ g.ss) and is a root or was reached earlier, reaches a section j named X, and either the policy is conservative or j is a root, then every section the run accesses is kept by GC (g.Live pol).
* **R6b.** For item-level references E, root items R and item i: if the section assignment sec' factors through sec (sec' j = f (sec j) for every item j, for a map f that merges sections) and i is kept under sec, then i is kept under sec'.
* **R7a.** For every GC input g and name X: if no relocation edge reaches a section named X and no section named X is a root, then under the precise start/stop policy no section named X is kept; and if, in addition, a section kept under the precise policy references the bounds of X, the bounds are undefined (StartStopUndefined, the toy's link failure).
* **R7f.** For every GC input g, policy pol and name X: if no relocation edge reaches a section named X, then GC keeps every section named X iff, for every section j named X, either j is a root, or the policy is conservative and some kept section references the bounds of X.
* **R8a.** For every program p (statics, each emitted into its own input section, and source-level link edges p.ledges) and static i: i survives end-to-end (the compiler stage emits it and linker GC keeps its section in the object the compiler produced) iff there is a path in p.ledges from a static whose section is a link root or retained to i, every static of which, the start and i included, the compiler stage keeps (it is referenced by compiler-kept code or compiler-used).
* **R8b.** (i) In Prog2.mk [stMain, stUsedOnly] [], the compiler-used static 1, in its own section and neither retained nor reachable at link time, survives the compiler stage and is removed by linker GC. (ii) In Prog2.mk [stMain, stRetainOnly] [], static 1, whose section carries the retain flag but which is neither referenced at compile time nor compiler-used, is dropped by the compiler stage and does not survive. (iii) In Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)], static 2 is compiler-used and reachable from the entry static 0 in the source-level link graph, but its sole path passes through static 1, which no flag keeps and the compiler stage drops; static 2 does not survive.

Non-claims for every result are listed in its card under Findings and collected, per result, under Boundaries (Non-claims). Read them before relying on a result.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Scope and model–system relation.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the
corresponding claims about any real dynamic loader, linker or compiler. Every connection to a real system below is
labelled `derived (modeling bridge)` and rests on the quoted documentation or source, not on the Lean proofs.

The RELRO model (results R1–R5) and the section-GC model (results R6–R8) are separate toy models with no proved
interaction between them; nothing in this package establishes or refutes how section GC affects RELRO segment
boundaries, page alignment, or the retention of statics placed in `.data.rel.ro`.

**Model fidelity.** This is a toy model. What its definitions are meant to capture, and the known gaps:

**RELRO model (`lean/ToyRelroGc/Relro/Model.lean`).**
* An image is a `List Kind`; byte `a` has kind `kinds[a]` (`code`, `ro` = `.rodata`, `relro` = `.data.rel.ro` / GOT
  entries inside the `PT_GNU_RELRO` range, `mutable` = `.data`/`.bss`); addresses at or past the length are unmapped.
  Memory (`Mem`) holds one natural number per address; a slot is one address (no word size, no byte encoding). Symbols
  (`Sym`) are numbers and a symbol table (`SymTab`) maps each symbol to an address.
* Map-time permissions are per byte: exactly `relro` and `mutable` bytes are writable (`mapWr`). This abstracts the
  linker's page-aligned segment layout at map time; page granularity enters at `protect` alone (results R4a–R4g). The
  model tracks write permission alone; read and execute permissions are not modeled.
* A relocation (`Reloc`) is a slot plus `val : SymTab → Mem → Nat`. `Reloc.AddressOnly` relocations ignore memory;
  resolver relocations (IFUNC-like) may read it (`Reloc.ReadsOnly`). Implicit-addend relocations would read their own
  slot and are not address-only.
* The loader runs a timeline of events: `apply r` (faults, leaving the state unchanged, if the slot is not currently
  writable), `protect` (makes the addresses in `c.prot` non-writable; never makes anything writable), and program
  operations `write a v` (faults on non-writable addresses) and `call x` (jumps to the address in `x`; if `x` is a lazy
  slot still holding `stub`, the lazy resolver first writes the target address into `x`, faulting if `x` is not
  writable). After a fault the run continues; outcomes are recorded per event.
* `timeline c ops k` is the schedule generator used by R1: relocations in list order, then `ops`, with one `protect`
  inserted at position `k`. `twoPhase c ops` is the case `k = c.relocs.length`. Claims about runs quantify over
  timelines produced by these generators, never over all interleavings.
* `CallWorks c sa x t` runs the one-operation program `[call x]` immediately after entry; programs with earlier
  operations are not covered by it.
* PIC versus link-time resolution: dynamic relocations (`c.relocs`) are applied at load time; `linkResolve saL c` models
  a link under the link-time table `saL`, which applies the relocations to the file image and leaves none. The model does
  not relate `saL` to the load-time table.
* Rounding policies: `downDown` = `[alignDown P rs, alignDown P re)`, `downUp` = `[alignDown P rs, alignUp P re)` when
  `rs < re` and empty otherwise, `exact` = `[rs, re)`, with `alignDown P a = a / P * P` and
  `alignUp P a = (a + P - 1) / P * P` (floor division, truncated subtraction; both are `0` when `P = 0`). An empty or
  inverted range protects nothing under every policy (`roundedMask_eq_false_of_le`). Addresses are unbounded `Nat`: no
  fixed-width wrap-around, no load bias.
* **Known gaps:** one object (no inter-object symbol resolution order, no `dlopen`), one `protect`, no text relocations,
  no execute permission, no copy relocations, no TLS, no concurrency, no permission changes requested by the program,
  lazy binding checked for the one-operation program `[call x]`.

**GC model (`lean/ToyRelroGc/Gc/Model.lean`).**
* Sections `0 .. n-1` with a name (a number standing for the `X` of `__start_X`) and four root-class flags (`entry`,
  `exported`, `keep` for `KEEP`, `retain` for `SHF_GNU_RETAIN`). Relocation edges `(i, j)`; start/stop references
  `(i, X)`. The `conservative` policy adds an edge from `i` to every section named `X`; `precise` adds none. Edge and
  reference endpoints are not checked against the number of sections: an index past the end names no section and is
  never a root, but it can be reached along a dangling edge (`phantom_section_live`).
* GC keeps exactly the sections reachable from roots (`GcIn.Live`). A run is a list of accesses (`Acc`), classified by
  how the program obtains the address: along a relocation edge (`edge i j`), by iterating from `__start_X` to `__stop_X`
  (`bounds i X j`), or through an address the linker cannot see (`implicit j`). The classification does not depend on
  the policy. Behaviour preservation is modeled as "every accessed section is kept" (`RunPreserved`).
* Granularity: items (functions, objects, bytes) are assigned to sections by `sec`; item references induce section
  edges; a section is a root if it contains a root item.
* An undefined `__start_X`/`__stop_X` (a kept section references the bounds of `X` but no section named `X` is kept) is
  modeled as a link failure (`StartStopUndefined`). When no section is named `X`, `RegistryKept` holds vacuously and
  `StartStopUndefined` holds (`empty_registry_kept_and_undefined`).
* Two-stage retention: statics with independent flags `cref` (referenced at compile time by code the compiler keeps),
  `cused` (compiler-used set), `retain` (retain flag on its output section), `lroot` (other link root). The compiler
  stage keeps `cref || cused`; each surviving static has its own input section; linker GC runs on the surviving
  statics.
* **Known gaps:** no section sizes or addresses, no `/DISCARD/`, no C-identifier condition on names, no weak
  references, no linker-script definitions of the bounds, no COMDAT groups, no `SHF_LINK_ORDER`, no static-archive
  member selection, no LTO, no compiler optimizations beyond dropping unreferenced, unused statics.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only; no Mathlib, no `Std` import and no other dependency (`lean/lakefile.toml` declares one `[[lean_lib]]`, `ToyRelroGc`, and no `[[require]]`).

**Subjects and how they relate.** `REPORT.json` lists the Lean toolchain release that checks every proof; the papers cited as prior art (Bernstein 1966 for the relocation-order results, Morrisett, Felleisen and Harper 1995 for reachability-based garbage-collection soundness, Gammie, Hosking and Engelhardt 2015 as related mechanized garbage-collection verification, Kell, Mulligan and Sewell 2016 and Wang, Xu, Wilke and Shao 2020 as related mechanized ELF linking); and the pinned upstream revisions (binutils 2.42 and 2.36, LLVM 19.1.0, glibc 2.40, musl 1.2.5, FreeBSD `releng/14.1`, Android Bionic `android14-release`, GCC 11.1.0, the Rust Reference) whose documentation or source is quoted in `derived (modeling bridge)` prose. The findings are statements about the toy model as checked by the toolchain. The upstream revisions are cited for their documented behaviour at those revisions; the package neither examines nor claims anything about their behaviour at other revisions, and none of them is modeled by a proved relation.

**Degenerate edges.** Page size `P = 0`: `alignDown 0 a = alignUp 0 a = 0` (floor division by zero is `0` in Lean), so the down-down and down-up masks are empty; results that need a positive page size assume `P > 0`, and R4b and R4e state the `P = 0` case explicitly. Empty RELRO range `rs = re`: every policy protects nothing (`roundedMask_eq_false_of_le`); R4b, R4d and R4g assume `rs < re`, which is tight (`downDown_coversRelro_iff_cex_empty`, `downUp_avoidsMut_iff_cex_empty`, `exists_pageGranular_iff_cex_empty`). Addresses are unbounded `Nat`, so there is no wrap-around at the end of an address space. GC edges may point past the last section (`phantom_section_live`); a name with no section makes its registry vacuously kept and its bounds undefined (`empty_registry_kept_and_undefined`).

## Findings

Basis for every Lean statement in this section: execution (Lean kernel check). Every claim that relates the toy to a real loader, linker or compiler is a separate `derived (modeling bridge)` claim, marked where it occurs (in the Basis lines of each card, in prior-art entries, and in the modeling-bridge notes at the end of this section).

Each card gives: the plain claim; kind, tier and depth; the Lean statement (verbatim, with any unfolding labelled as prose or checked); the hypothesis ledger (in which `tight` means that a named theorem exhibits an instance of the stated witness class satisfying all the other hypotheses while the conclusion fails); the non-vacuity witness; for impossibility results, a positive control; non-claims; prior art; the basis lines; and the design question it informs.

### Key definitions (verbatim)

```lean
-- lean/ToyRelroGc/Relro/Model.lean:15
abbrev Mem := Nat → Nat
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:17
abbrev Sym := Nat
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:19
abbrev SymTab := Sym → Nat
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:22
def upd (m : Mem) (a v : Nat) : Mem := fun b => if b = a then v else m b
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:27-32
inductive Kind where
  | code
  | ro
  | relro
  | mutable
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:37-39
structure Reloc where
  slot : Nat
  val : SymTab → Mem → Nat
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:42-43
def Reloc.AddressOnly (r : Reloc) : Prop :=
  ∀ (sa : SymTab) (m m' : Mem), r.val sa m = r.val sa m'
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:46-47
def Reloc.ReadsOnly (r : Reloc) (S : Nat → Prop) : Prop :=
  ∀ (sa : SymTab) (m m' : Mem), (∀ a, S a → m a = m' a) → r.val sa m = r.val sa m'
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:50
def applyReloc (sa : SymTab) (m : Mem) (r : Reloc) : Mem := upd m r.slot (r.val sa m)
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:53
def applyAll (sa : SymTab) (rs : List Reloc) (m : Mem) : Mem := rs.foldl (applyReloc sa) m
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:59-65
structure Cfg where
  kinds : List Kind
  init : Mem
  relocs : List Reloc
  prot : Nat → Bool
  lazy : List (Nat × Sym)
  stub : Nat
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:70-74
def mapWr (L : List Kind) (a : Nat) : Bool :=
  match L[a]? with
  | some .relro => true
  | some .mutable => true
  | _ => false
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:77-79
structure St where
  mem : Mem
  wr : Nat → Bool
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:82
def Cfg.start (c : Cfg) : St := ⟨c.init, mapWr c.kinds⟩
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:85-87
inductive Op where
  | write (a v : Nat)
  | call (x : Nat)
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:91-94
inductive Ev where
  | apply (r : Reloc)
  | protect
  | op (o : Op)
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:97-101
inductive Out where
  | ok
  | fault
  | jump (d : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:104-105
def stepApply (sa : SymTab) (s : St) (r : Reloc) : St × Out :=
  if s.wr r.slot then ({ s with mem := applyReloc sa s.mem r }, .ok) else (s, .fault)
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:108
def stepProtect (c : Cfg) (s : St) : St := { s with wr := fun a => s.wr a && !c.prot a }
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:113-118
def stepOp (c : Cfg) (sa : SymTab) (s : St) : Op → St × Out
  | .write a v => if s.wr a then ({ s with mem := upd s.mem a v }, .ok) else (s, .fault)
  | .call x =>
    match (if s.mem x = c.stub then c.lazy.lookup x else none) with
    | some t => if s.wr x then ({ s with mem := upd s.mem x (sa t) }, .jump (sa t)) else (s, .fault)
    | none => (s, .jump (s.mem x))
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:122-125
structure Trace where
  applyOuts : List Out
  opOuts : List Out
  memAtProtect : Option Mem
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:128-140
def runT (c : Cfg) (sa : SymTab) : St → List Ev → Trace
  | _, [] => ⟨[], [], none⟩
  | s, .apply r :: t =>
    let p := stepApply sa s r
    let tr := runT c sa p.1 t
    { tr with applyOuts := p.2 :: tr.applyOuts }
  | s, .protect :: t =>
    let tr := runT c sa (stepProtect c s) t
    { tr with memAtProtect := some s.mem }
  | s, .op o :: t =>
    let p := stepOp c sa s o
    let tr := runT c sa p.1 t
    { tr with opOuts := p.2 :: tr.opOuts }
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:143
def trace (c : Cfg) (sa : SymTab) (t : List Ev) : Trace := runT c sa c.start t
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:146
def insertAt {α : Type} (k : Nat) (x : α) (l : List α) : List α := l.take k ++ x :: l.drop k
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:150-151
def timeline (c : Cfg) (ops : List Op) (k : Nat) : List Ev :=
  insertAt k .protect (c.relocs.map .apply ++ ops.map .op)
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:154-155
def twoPhase (c : Cfg) (ops : List Op) : List Ev :=
  c.relocs.map .apply ++ .protect :: ops.map .op
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:158
def LoadOk (tr : Trace) : Prop := ∀ o ∈ tr.applyOuts, o = .ok
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:166
def RelocSlotsWritable (c : Cfg) : Prop := ∀ r ∈ c.relocs, mapWr c.kinds r.slot = true
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:169-170
def CoversRelro (L : List Kind) (m : Nat → Bool) : Prop :=
  ∀ a < L.length, L[a]? = some .relro → m a = true
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:173-174
def AvoidsMut (L : List Kind) (m : Nat → Bool) : Prop :=
  ∀ a < L.length, L[a]? = some .mutable → m a = false
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:183
def ProtCoversRelro (c : Cfg) : Prop := CoversRelro c.kinds c.prot
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:186
def ProtAvoidsMut (c : Cfg) : Prop := AvoidsMut c.kinds c.prot
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:201-207
def TwoPhaseGuarantees (c : Cfg) (sa : SymTab) (ops : List Op) (k : Nat) : Prop :=
  let tr := trace c sa (timeline c ops k)
  LoadOk tr ∧ tr.memAtProtect = some (applyAll sa c.relocs c.init) ∧
  (∀ j a v : Nat, ops[j]? = some (Op.write a v) → c.kinds[a]? = some Kind.relro →
    tr.opOuts[j]? = some Out.fault) ∧
  (∀ j a v : Nat, ops[j]? = some (Op.write a v) → c.kinds[a]? = some Kind.mutable →
    tr.opOuts[j]? = some Out.ok)
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:213-215
def WriteFaultsAfter (c : Cfg) (sa : SymTab) (a : Nat) : Prop :=
  ∀ (ops : List Op) (v : Nat),
    (trace c sa (twoPhase c (ops ++ [.write a v]))).opOuts[ops.length]? = some .fault
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:221-222
def linkResolve (saL : SymTab) (c : Cfg) : Cfg :=
  { c with init := applyAll saL c.relocs c.init, relocs := [] }
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:225
def bindReloc (x : Nat) (t : Sym) : Reloc := ⟨x, fun sa _ => sa t⟩
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:230-232
def EagerBound (c : Cfg) (x : Nat) (t : Sym) : Prop :=
  bindReloc x t ∈ c.relocs ∧ (∀ r ∈ c.relocs, r.slot = x → r = bindReloc x t) ∧
  c.lazy.lookup x = none
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:236-237
def LazyBound (c : Cfg) (x : Nat) (t : Sym) : Prop :=
  c.lazy.lookup x = some t ∧ c.init x = c.stub ∧ ∀ r ∈ c.relocs, r.slot ≠ x
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:244-246
def CallWorks (c : Cfg) (sa : SymTab) (x : Nat) (t : Sym) : Prop :=
  let tr := trace c sa (twoPhase c [.call x])
  LoadOk tr ∧ tr.opOuts = [.jump (sa t)]
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:251
def alignDown (P a : Nat) : Nat := a / P * P
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:254
def alignUp (P a : Nat) : Nat := (a + P - 1) / P * P
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:259-263
inductive Rounding where
  | downDown
  | downUp
  | exact
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:266
def rangeMask (lo hi : Nat) : Nat → Bool := fun a => decide (lo ≤ a ∧ a < hi)
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:274-278
def roundedMask (pol : Rounding) (P rs re : Nat) : Nat → Bool :=
  match pol with
  | .downDown => rangeMask (alignDown P rs) (alignDown P re)
  | .downUp => if rs < re then rangeMask (alignDown P rs) (alignUp P re) else fun _ => false
  | .exact => rangeMask rs re
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:281-282
def RelroIs (L : List Kind) (rs re : Nat) : Prop :=
  rs ≤ re ∧ re ≤ L.length ∧ ∀ a < L.length, (L[a]? = some .relro ↔ (rs ≤ a ∧ a < re))
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:289
def NoMutIn (L : List Kind) (lo hi : Nat) : Prop := ∀ a < hi, lo ≤ a → L[a]? ≠ some .mutable
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:296
def PageGranular (P : Nat) (m : Nat → Bool) : Prop := ∀ a b, a / P = b / P → m a = m b
```

```lean
-- lean/ToyRelroGc/Relro/Model.lean:299-300
def NoSharedPage (P : Nat) (L : List Kind) : Prop :=
  ∀ a < L.length, ∀ b < L.length, a / P = b / P → L[a]? = some .relro → L[b]? ≠ some .mutable
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:235-237
def EagerRelroOrLazyMut (c : Cfg) (B : List (Nat × Sym)) : Prop :=
  ∀ b ∈ B, (EagerBound c b.1 b.2 ∧ c.kinds[b.1]? = some .relro) ∨
    (LazyBound c b.1 b.2 ∧ c.kinds[b.1]? = some .mutable)
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:241-242
def EagerRelroOrLazy (c : Cfg) (B : List (Nat × Sym)) : Prop :=
  ∀ b ∈ B, (EagerBound c b.1 b.2 ∧ c.kinds[b.1]? = some .relro) ∨ LazyBound c b.1 b.2
```

```lean
-- lean/ToyRelroGc/Relro/Basic.lean:10-11
def tryApplyAll (sa : SymTab) (w : Nat → Bool) (rs : List Reloc) (m : Mem) : Mem :=
  rs.foldl (fun m r => if w r.slot then applyReloc sa m r else m) m
```

```lean
-- lean/ToyRelroGc/Relro/Basic.lean:15-16
def postLoad (c : Cfg) (sa : SymTab) : St :=
  ⟨tryApplyAll sa (mapWr c.kinds) c.relocs c.init, fun a => mapWr c.kinds a && !c.prot a⟩
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:9-11
inductive Reach (E : List (Nat × Nat)) (R : Nat → Prop) : Nat → Prop where
  | root {i : Nat} : R i → Reach E R i
  | step {i j : Nat} : Reach E R i → (i, j) ∈ E → Reach E R j
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:18-24
structure Sec where
  name : Nat
  entry : Bool
  exported : Bool
  keep : Bool
  retain : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:27
def Sec.isRoot (s : Sec) : Bool := s.entry || s.exported || s.keep || s.retain
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:34-37
structure GcIn where
  secs : List Sec
  edges : List (Nat × Nat)
  ss : List (Nat × Nat)
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:42-45
inductive SSPolicy where
  | conservative
  | precise
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:48-51
def GcIn.isRootB (g : GcIn) (i : Nat) : Bool :=
  match g.secs[i]? with
  | some s => s.isRoot
  | none => false
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:54
def GcIn.IsRoot (g : GcIn) (i : Nat) : Prop := g.isRootB i = true
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:57
def GcIn.nameOf (g : GcIn) (i : Nat) : Option Nat := (g.secs[i]?).map Sec.name
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:61-64
def GcIn.ssEdges (g : GcIn) : SSPolicy → List (Nat × Nat)
  | .conservative => g.ss.flatMap fun e =>
      ((List.range g.secs.length).filter fun j => g.nameOf j == some e.2).map fun j => (e.1, j)
  | .precise => []
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:68
def GcIn.Live (g : GcIn) (pol : SSPolicy) : Nat → Prop := Reach (g.edges ++ g.ssEdges pol) g.IsRoot
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:81-85
inductive Acc where
  | edge (i j : Nat)
  | bounds (i X j : Nat)
  | implicit (j : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:88-91
def Acc.dst : Acc → Nat
  | .edge _ j => j
  | .bounds _ _ j => j
  | .implicit j => j
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:94-95
def ReachedBefore (R : Nat → Prop) (run : List Acc) (k i : Nat) : Prop :=
  R i ∨ ∃ k' < k, ∃ a : Acc, run[k']? = some a ∧ a.dst = i
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:99-100
def EdgeAccessesFollowEdges (E : List (Nat × Nat)) (R : Nat → Prop) (run : List Acc) : Prop :=
  ∀ k i j : Nat, run[k]? = some (Acc.edge i j) → (i, j) ∈ E ∧ ReachedBefore R run k i
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:103-104
def ImplicitAccessesHitRoots (R : Nat → Prop) (run : List Acc) : Prop :=
  ∀ k j : Nat, run[k]? = some (Acc.implicit j) → R j
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:109-112
def BoundsAccessesRetained (g : GcIn) (pol : SSPolicy) (run : List Acc) : Prop :=
  ∀ k i X j : Nat, run[k]? = some (Acc.bounds i X j) →
    (i, X) ∈ g.ss ∧ g.nameOf j = some X ∧ ReachedBefore g.IsRoot run k i ∧
      (pol = .conservative ∨ g.IsRoot j)
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:115-116
def RunPreserved (g : GcIn) (pol : SSPolicy) (run : List Acc) : Prop :=
  ∀ a ∈ run, g.Live pol a.dst
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:122-123
def secEdges (sec : Nat → Nat) (E : List (Nat × Nat)) : List (Nat × Nat) :=
  E.map fun e => (sec e.1, sec e.2)
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:126
def secRoot (sec : Nat → Nat) (R : Nat → Prop) : Nat → Prop := fun s => ∃ i, R i ∧ sec i = s
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:129-130
def KeptItem (sec : Nat → Nat) (E : List (Nat × Nat)) (R : Nat → Prop) (i : Nat) : Prop :=
  Reach (secEdges sec E) (secRoot sec R) (sec i)
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:135-136
def RegistryKept (g : GcIn) (pol : SSPolicy) (X : Nat) : Prop :=
  ∀ j, g.nameOf j = some X → g.Live pol j
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:140-141
def registryScan (g : GcIn) (i X : Nat) : List Acc :=
  ((List.range g.secs.length).filter fun j => g.nameOf j == some X).map (Acc.bounds i X)
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:145-146
def StartStopUndefined (g : GcIn) (pol : SSPolicy) (X : Nat) : Prop :=
  (∃ i, g.Live pol i ∧ (i, X) ∈ g.ss) ∧ ∀ j, g.nameOf j = some X → ¬ g.Live pol j
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:150
def NoEdgeIntoName (g : GcIn) (X : Nat) : Prop := ∀ e ∈ g.edges, g.nameOf e.2 ≠ some X
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:158-163
structure Static where
  cref : Bool
  cused : Bool
  retain : Bool
  lroot : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:167-169
structure Prog2 where
  statics : List Static
  ledges : List (Nat × Nat)
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:172
def compileKeeps (s : Static) : Bool := s.cref || s.cused
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:175-178
def Prog2.compiled (p : Prog2) (i : Nat) : Bool :=
  match p.statics[i]? with
  | some s => compileKeeps s
  | none => false
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:181-182
def Prog2.objEdges (p : Prog2) : List (Nat × Nat) :=
  p.ledges.filter fun e => p.compiled e.1 && p.compiled e.2
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:185-186
def Prog2.objRoot (p : Prog2) (i : Nat) : Prop :=
  p.compiled i = true ∧ ∃ s, p.statics[i]? = some s ∧ (s.lroot || s.retain) = true
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:189
def Prog2.LinkReach (p : Prog2) (i : Nat) : Prop := Reach p.objEdges p.objRoot i
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:192
def Prog2.Survives (p : Prog2) (i : Nat) : Prop := p.compiled i = true ∧ p.LinkReach i
```

```lean
-- lean/ToyRelroGc/Gc/Model.lean:196-202
inductive Prog2.CompiledPath (p : Prog2) : Nat → Prop where
  | root {i : Nat} {s : Static} :
      p.statics[i]? = some s → compileKeeps s = true → (s.lroot || s.retain) = true →
      Prog2.CompiledPath p i
  | step {i j : Nat} {sj : Static} :
      Prog2.CompiledPath p i → (i, j) ∈ p.ledges → p.statics[j]? = some sj →
      compileKeeps sj = true → Prog2.CompiledPath p j
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:662-663
def Prog2.SrcReach (p : Prog2) (i : Nat) : Prop :=
  Reach p.ledges (fun j => ∃ s, p.statics[j]? = some s ∧ (s.lroot || s.retain) = true) i
```

### Concrete instances (verbatim)

```lean
-- lean/ToyRelroGc/Relro/Examples.lean:9
def sa0 : SymTab := fun s => 100 + s
```

```lean
-- lean/ToyRelroGc/Relro/Examples.lean:12
def symReloc (x : Nat) (t : Sym) : Reloc := ⟨x, fun sa _ => sa t⟩
```

```lean
-- lean/ToyRelroGc/Relro/Examples.lean:16-22
def goodCfg : Cfg where
  kinds := [.relro, .mutable]
  init := fun _ => 0
  relocs := [symReloc 0 0]
  prot := rangeMask 0 1
  lazy := []
  stub := 0
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:55
def cfgSlotRo : Cfg := { goodCfg with kinds := [.ro], prot := fun _ => false }
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:65-71
def cfgTwoRelro : Cfg where
  kinds := [.relro, .relro]
  init := fun _ => 0
  relocs := [symReloc 0 0, symReloc 1 1]
  prot := rangeMask 0 2
  lazy := []
  stub := 0
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:94
def cfgNoProt : Cfg := { goodCfg with prot := fun _ => false }
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:106
def cfgProtMut : Cfg := { goodCfg with prot := rangeMask 0 2 }
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:14
def eagerCfg : Cfg := ⟨[.relro], fun _ => 0, [bindReloc 0 0], rangeMask 0 1, [], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:17
def lazyRelroCfg : Cfg := ⟨[.relro], fun _ => 0, [], rangeMask 0 1, [(0, 0)], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:20
def lazyMutCfg : Cfg := ⟨[.mutable], fun _ => 0, [], fun _ => false, [(0, 0)], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:24
def mixedCfg : Cfg := ⟨[.relro, .mutable], fun _ => 0, [bindReloc 0 0], rangeMask 0 1, [(1, 1)], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:109
def eagerMutCfg : Cfg := ⟨[.mutable], fun _ => 0, [bindReloc 0 0], fun _ => false, [], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:245
def cfgMutReloc : Cfg := ⟨[.mutable], fun _ => 0, [symReloc 0 0], fun _ => false, [], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:312
def cfgMutCovered : Cfg := ⟨[.mutable], fun _ => 0, [symReloc 0 0], rangeMask 0 1, [], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:334-335
def cfgRoMutReloc : Cfg :=
  ⟨[.ro, .mutable], fun _ => 0, [symReloc 0 0, symReloc 1 0], fun _ => false, [], 0⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:364
def cfgRelroRo : Cfg := ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:303
def layoutRelro3 : List Kind := [.relro, .relro, .relro]
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:305
def layoutRelro3Mut : List Kind := [.relro, .relro, .relro, .mutable]
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:307
def layoutMutRelro : List Kind := [.mutable, .relro]
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:310-311
def protCfg (layout : List Kind) (m : Nat → Bool) : Cfg :=
  ⟨layout, fun _ => 0, [], m, [], 0⟩
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:508
def rAddr0 : Reloc := symReloc 0 0
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:510
def rRes1 : Reloc := ⟨1, fun _ m => m 0⟩
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:545
def rRes2of1 : Reloc := ⟨2, fun _ m => m 1⟩
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:568
def rConst0 : Reloc := ⟨0, fun _ _ => 5⟩
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:643
def rRes3of2 : Reloc := ⟨3, fun _ m => m 2⟩
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:646
def rRes4of9 : Reloc := ⟨4, fun _ m => m 9⟩
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:203-206
def gcPair (edges : List (Nat × Nat)) : GcIn where
  secs := [⟨0, true, false, false, false⟩, ⟨1, false, false, false, false⟩]
  edges := edges
  ss := []
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:456
def mkSec (name : Nat) (entry keep retain : Bool) : Sec := ⟨name, entry, false, keep, retain⟩
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:460-463
def gcReg (edges : List (Nat × Nat)) (keep retain : Bool) : GcIn where
  secs := [mkSec 0 true false false, mkSec 7 false keep retain, mkSec 7 false keep retain]
  edges := edges
  ss := [(0, 7)]
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:728-729
def gcDeadRef : GcIn := ⟨[mkSec 0 true false false, mkSec 5 false false false,
  mkSec 7 false false false], [], [(1, 7)]⟩
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:883-886
def gcPhantom : GcIn where
  secs := [mkSec 0 true false false, mkSec 7 false false false]
  edges := [(0, 99)]
  ss := [(99, 7)]
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:900-903
def gcEmptyReg : GcIn where
  secs := [mkSec 0 true false false]
  edges := []
  ss := [(0, 7)]
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:324
def itemEdges : List (Nat × Nat) := [(0, 1)]
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:327
def itemRoot (i : Nat) : Prop := i = 0
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:330
def secFine (i : Nat) : Nat := i
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:333
def secShared (i : Nat) : Nat := if i = 2 then 1 else i
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:632
def stMain : Static := ⟨true, false, false, true⟩
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:634
def stUsedOnly : Static := ⟨false, true, false, false⟩
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:636
def stRetainOnly : Static := ⟨false, false, true, false⟩
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:638
def stUsedRetained : Static := ⟨false, true, true, false⟩
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:667
def stPlain : Static := ⟨false, false, false, false⟩
```

### Definition examples (proved)

Positive and negative examples of the core definitions; each is a kernel-checked theorem.

```lean
-- lean/ToyRelroGc/Witnesses.lean:393
theorem addressOnly_examples : (symReloc 0 0).AddressOnly ∧ ¬ rRes1.AddressOnly :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:402
theorem readsOnly_examples : rRes1.ReadsOnly (fun a => a = 0) ∧ ¬ rRes1.ReadsOnly (fun _ => False) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:409-411
theorem mapWr_examples :
    mapWr [.relro, .mutable] 0 = true ∧ mapWr [.relro, .mutable] 1 = true ∧
      mapWr [.ro] 0 = false ∧ mapWr [.code] 0 = false ∧ mapWr [.relro] 5 = false := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:417-422
theorem loader_predicate_examples :
    RelocSlotsWritable goodCfg ∧ ¬ RelocSlotsWritable cfgSlotRo ∧
      ProtCoversRelro goodCfg ∧ ¬ ProtCoversRelro cfgNoProt ∧
      ProtAvoidsMut goodCfg ∧ ¬ ProtAvoidsMut cfgProtMut ∧
      LoadOk (trace goodCfg sa0 (twoPhase goodCfg [])) ∧
      ¬ LoadOk (trace cfgSlotRo sa0 (twoPhase cfgSlotRo [])) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:427-429
theorem twoPhaseGuarantees_examples :
    TwoPhaseGuarantees goodCfg sa0 [.write 0 5, .write 1 5] 1 ∧
      ¬ TwoPhaseGuarantees goodCfg sa0 [.write 0 9] 2 :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:435-436
theorem writeFaultsAfter_examples :
    WriteFaultsAfter goodCfg sa0 0 ∧ ¬ WriteFaultsAfter goodCfg sa0 1 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:442-444
theorem linkResolve_examples :
    (linkResolve sa0 goodCfg).relocs = [] ∧ (linkResolve sa0 goodCfg).init 0 = 100 ∧
      goodCfg.init 0 ≠ (linkResolve sa0 goodCfg).init 0 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:448-451
theorem binding_examples :
    EagerBound eagerCfg 0 0 ∧ ¬ EagerBound lazyRelroCfg 0 0 ∧
      LazyBound lazyRelroCfg 0 0 ∧ ¬ LazyBound eagerCfg 0 0 ∧
      CallWorks eagerCfg sa0 0 0 ∧ ¬ CallWorks lazyRelroCfg sa0 0 0 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:458-459
theorem eagerRelroOrLazyMut_examples :
    EagerRelroOrLazyMut mixedCfg [(0, 0), (1, 1)] ∧ ¬ EagerRelroOrLazyMut lazyRelroCfg [(0, 0)] :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:953-955
theorem eagerRelroOrLazy_examples :
    EagerRelroOrLazy mixedCfg [(0, 0), (1, 1)] ∧ EagerRelroOrLazy lazyRelroCfg [(0, 0)] ∧
      ¬ EagerRelroOrLazy eagerMutCfg [(0, 0)] :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:464-466
theorem align_examples :
    alignDown 4 5 = 4 ∧ alignUp 4 5 = 8 ∧ alignDown 4 8 = 8 ∧ alignUp 4 8 = 8 ∧
      alignDown 0 5 = 0 ∧ alignUp 0 5 = 0 ∧ alignUp 4 0 = 0 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:471-474
theorem roundedMask_examples :
    roundedMask .downDown 4 1 9 0 = true ∧ roundedMask .downDown 4 1 9 8 = false ∧
      roundedMask .downUp 4 1 9 11 = true ∧ roundedMask .downUp 4 1 9 12 = false ∧
      roundedMask .exact 4 1 9 0 = false ∧ roundedMask .exact 4 1 9 8 = true := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:960-962
theorem roundedMask_empty_examples :
    roundedMask .downUp 2 1 1 0 = false ∧ roundedMask .downDown 2 1 1 0 = false ∧
      roundedMask .exact 2 1 1 1 = false ∧ roundedMask .downUp 2 1 2 0 = true := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:479-480
theorem relroIs_examples :
    RelroIs layoutRelro3 0 3 ∧ ¬ RelroIs layoutRelro3 0 2 ∧ ¬ RelroIs layoutRelro3Mut 0 4 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:484-485
theorem noMutIn_examples :
    NoMutIn layoutRelro3Mut 0 3 ∧ ¬ NoMutIn layoutRelro3Mut 3 4 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:489
theorem pageGranular_examples : PageGranular 2 (rangeMask 0 4) ∧ ¬ PageGranular 2 (rangeMask 0 3) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:496-497
theorem noSharedPage_examples :
    NoSharedPage 2 [.relro, .relro, .mutable] ∧ ¬ NoSharedPage 2 layoutRelro3Mut := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:504-507
theorem sec_isRoot_examples :
    (mkSec 0 false true false).isRoot = true ∧ (mkSec 0 false false true).isRoot = true ∧
      (⟨0, false, true, false, false⟩ : Sec).isRoot = true ∧
      (mkSec 0 false false false).isRoot = false := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:512
theorem live_examples (pol : SSPolicy) : (gcPair [(0, 1)]).Live pol 1 ∧ ¬ (gcPair []).Live pol 1 :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:517-519
theorem ssEdges_examples :
    (0, 2) ∈ (gcReg [] false false).ssEdges .conservative ∧
      (gcReg [] false false).ssEdges .precise = [] := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:523-525
theorem runPreserved_examples (pol : SSPolicy) :
    RunPreserved (gcPair [(0, 1)]) pol [.implicit 0, .edge 0 1] ∧
      ¬ RunPreserved (gcPair []) pol [.implicit 1] :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:532-533
theorem keptItem_examples :
    KeptItem secFine itemEdges itemRoot 1 ∧ ¬ KeptItem secFine itemEdges itemRoot 2 :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:537-542
theorem registry_examples :
    RegistryKept (gcReg [] false false) .conservative 7 ∧
      ¬ RegistryKept (gcReg [(0, 1)] false false) .precise 7 ∧
      StartStopUndefined (gcReg [] false false) .precise 7 ∧
      ¬ StartStopUndefined (gcReg [(0, 1)] false false) .precise 7 ∧
      NoEdgeIntoName (gcReg [] false false) 7 ∧ ¬ NoEdgeIntoName (gcReg [(0, 1)] false false) 7 :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:920-922
theorem registryScan_examples :
    registryScan (gcReg [] false false) 0 7 = [.bounds 0 7 1, .bounds 0 7 2] ∧
      registryScan (gcReg [] false false) 0 9 = [] := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:927-929
theorem registryScan_preserved_examples :
    RunPreserved (gcReg [] false false) .conservative (registryScan (gcReg [] false false) 0 7) ∧
      ¬ RunPreserved (gcReg [] false false) .precise (registryScan (gcReg [] false false) 0 7) :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:935-940
theorem access_predicate_examples :
    ReachedBefore (gcReg [] false false).IsRoot [.implicit 0, .bounds 0 7 1] 1 0 ∧
      ¬ ReachedBefore (gcReg [] false false).IsRoot [.implicit 0, .bounds 0 7 1] 1 1 ∧
      BoundsAccessesRetained (gcReg [] false false) .conservative
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] ∧
      ¬ BoundsAccessesRetained (gcReg [] false false) .precise [.implicit 0, .bounds 0 7 1] := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:548-551
theorem twoStage_examples :
    compileKeeps stUsedOnly = true ∧ compileKeeps stRetainOnly = false ∧
      (Prog2.mk [stMain, stUsedRetained] []).Survives 1 ∧
      ¬ (Prog2.mk [stMain, stUsedOnly] []).Survives 1 :=
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:685-687
theorem srcReach_examples :
    (Prog2.mk [stMain, stPlain] [(0, 1)]).SrcReach 1 ∧
      ¬ (Prog2.mk [stMain, stPlain] []).SrcReach 1 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:968-970
theorem compiledPath_examples :
    (Prog2.mk [stMain, stUsedRetained] []).CompiledPath 1 ∧
      ¬ (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).CompiledPath 2 :=
```

### R1 — `twoPhaseGuarantees_of_slotsWritable_of_protectAfterRelocs_of_covers_of_avoids`

**Plain claim.** For every loader input c, symbol table sa, program ops and protect position k, consider the timeline produced by `timeline c ops k` (the relocations of c in list order, then the program operations ops, with one protect event inserted at position k). If (H1) every relocated slot is mapped writable, (H2) k = c.relocs.length (protect right after the last relocation and before the first program operation), (H3) protect covers every RELRO byte, and (H4) protect covers no mutable byte, then no relocation faults, the memory at protect equals the fully relocated image applyAll sa c.relocs c.init, every program write to a RELRO byte faults, and every program write to a mutable byte succeeds.

**Kind / tier / depth.** theorem / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results.lean:19-23
theorem twoPhaseGuarantees_of_slotsWritable_of_protectAfterRelocs_of_covers_of_avoids
    (c : Cfg) (sa : SymTab) (ops : List Op) (k : Nat)
    (hWr : RelocSlotsWritable c) (hOrder : k = c.relocs.length)
    (hCover : ProtCoversRelro c) (hAvoid : ProtAvoidsMut c) :
    TwoPhaseGuarantees c sa ops k := by
```

Unfolded (prose): `TwoPhaseGuarantees c sa ops k` (quoted under Key definitions) is the conjunction: every outcome of an `apply` event of `trace c sa (timeline c ops k)` is `ok`; its `memAtProtect` is `some (applyAll sa c.relocs c.init)`; for every index `j` with `ops[j]? = some (write a v)` and `a` a RELRO byte, the `j`-th program outcome is `fault`; for every such `j` with `a` a mutable byte, it is `ok`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hWr : RelocSlotsWritable c` | relocations write their slots while they are applied | tight: `twoPhase_cex_slot_not_writable` (witness class: a toy loader input with at most two bytes and at most two relocations) |
| `hOrder : k = c.relocs.length` | protect after the last relocation and before entry (two violation modes) | tight: `twoPhase_cex_protect_before_last_reloc`, `twoPhase_cex_protect_after_entry` (witness class: a toy loader input with at most two bytes and at most two relocations) |
| `hCover : ProtCoversRelro c` | every RELRO byte becomes read-only (used by the third conclusion) | tight: `twoPhase_cex_prot_misses_relro` (witness class: a toy loader input with at most two bytes and at most two relocations) |
| `hAvoid : ProtAvoidsMut c` | mutable statics stay writable (used by the fourth conclusion) | tight: `twoPhase_cex_prot_covers_mut` (witness class: a toy loader input with at most two bytes and at most two relocations) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** goodCfg (byte 0 RELRO with one relocation, byte 1 mutable, protect covers exactly byte 0) with k = 1 satisfies all four hypotheses (twoPhase_nonvacuity); twoPhaseGuarantees_examples applies the theorem to it with ops = [write 0 5, write 1 5]. (`twoPhase_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The claim is for timelines produced by the generator timeline (relocations in list order, exactly one protect event inserted at position k). Several protect calls, several objects relocated one after another, concurrent threads, and permission changes requested by the program after entry are not modeled.
* Integrity here means that every program write to a RELRO byte faults. It says nothing about reads, about writes by the loader after entry (lazy binding is result R3), or about values written before protect. TwoPhaseGuarantees records the memory at protect and the outcomes of program writes; it states no invariance of memory contents across later program states, and writes by anything other than the program (debuggers, devices) are not modeled.
* It does not say how a real linker decides which bytes are RELRO, nor how protect is computed from page rounding (results R4a-R4g).
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The countermodels show each hypothesis is tight in this toy (loader inputs of at most two bytes); they do not show that every real loader violating a hypothesis is exploitable.

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1560-1563 (body of the item `relro` / `norelro`, lines 1558-1559; Texinfo markup removed): "Create an ELF PT_GNU_RELRO segment header in the object. This specifies a memory segment that should be made read-only after relocation, if supported. Specifying common-page-size smaller than the system page size will render this protection ineffective." Basis: documentation.
* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/dl-reloc.c lines 353-370, function _dl_protect_relro (paraphrase of the source): start = ALIGN_DOWN(l_addr + l_relro_addr, pagesize), end = ALIGN_DOWN(l_addr + l_relro_addr + l_relro_size, pagesize), and __mprotect(start, end - start, PROT_READ) is called only if start != end; line 301 of _dl_relocate_object calls ELF_DYNAMIC_RELOCATE, and lines 348-349 then run "if (l->l_relro_size != 0)" / "_dl_protect_relro (l);". Basis: source. Derived (modeling bridge): the toy's down-down policy has the same rounding shape (both ends rounded down), and the toy's two-phase timeline has the same relocate-then-protect order for one object. The protection requested is PROT_READ, which also withholds execute permission; the toy tracks write permission alone.
* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/elf.h line 729: "#define PT_GNU_RELRO 0x6474e552 /* Read-only after relocation */". Basis: source. The Linux Standard Base text for PT_GNU_RELRO was not verified (the hosting site served an automated bot-check page, which was not bypassed).
* S. Kell, D. P. Mulligan, P. Sewell, "The missing link: explaining ELF static linking, semantically", OOPSLA 2016, pp. 607-623, doi:10.1145/2983990.2983996: a Lem/Isabelle specification of static ELF linking; it states about --gc-sections "we currently do not model it" and restricts itself to static linking (no load-time relocation or RELRO protection).
* Y. Wang, X. Xu, P. Wilke, Z. Shao, "CompCertELF: verified separate compilation of C programs into ELF object files", Proceedings of the ACM on Programming Languages 4 (OOPSLA), 2020, pp. 1-28, doi:10.1145/3428265 (bibliographic record verified via Crossref; described here by its title, the paper text was not re-read for this package). Mechanized ELF object generation and linking; it is cited as related mechanized work, not as covering dynamic loading, RELRO protection or section GC.
* Novelty record: a bounded search (web search and Crossref, 2026-11-21) found the mechanized ELF-linking work of Kell, Mulligan and Sewell (doi:10.1145/2983990.2983996) and CompCertELF (doi:10.1145/3428265); no mechanized model of RELRO page rounding, linker GC retention roots, or compiler-then-linker retention was found. The tier is T1 (folklore made precise), not a novelty claim.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** RELRO: which load-time conditions (writability during relocation, protect placement, coverage of RELRO, non-coverage of mutable data) must a verified toolchain assume so that the program starts with the relocated image and immutable data is write-protected after entry?

### R2a — `pic_rodata_slot_load_faults`

**Plain claim.** If a dynamic relocation r of loader input c (r ∈ c.relocs, that is, r is applied by the loader at load time) writes a byte of kind ro (.rodata), then for every symbol table sa and program ops the two-phase load of c faults.

**Kind / tier / depth.** impossibility / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness, counterexample and positive control named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results.lean:121-123
theorem pic_rodata_slot_load_faults (c : Cfg) (sa : SymTab) (ops : List Op) (r : Reloc)
    (hr : r ∈ c.relocs) (hk : c.kinds[r.slot]? = some .ro) :
    ¬ LoadOk (trace c sa (twoPhase c ops)) := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hr : r ∈ c.relocs` | the relocation is applied by the loader at load time (as under PIC) | tight: `pic_rodata_cex_link_resolved` (witness class: a one-byte toy image after link-time resolution) |
| `hk : c.kinds[r.slot]? = some .ro` | the slot is a .rodata byte (not mapped writable) | tight: `pic_rodata_cex_relro_slot` (witness class: a toy loader input with at most two bytes and at most two relocations) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** cfgSlotRo (a one-byte .rodata image with one relocation of that byte) satisfies both hypotheses (first conjunct of placement_nonvacuity). (`placement_nonvacuity`)

**Positive control.** If the linker resolves the relocations of c into the file image under a link-time table saL (linkResolve saL c, which leaves no dynamic relocation), then for every load-time table saR a .rodata byte s loads without fault, has post-entry write protection, and the image at protect equals applyAll saL c.relocs c.init. (`linkResolved_rodata_loadOk_writeFaultsAfter_and_image`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Code bytes and unmapped addresses also fault in the toy (mapWr is false for them), but this card states the .rodata case alone.
* The toy has no mechanism that makes read-only pages temporarily writable during relocation (text relocations); the claim neither establishes nor refutes anything about loaders that have one.
* This applies to slots written by a dynamic relocation (r ∈ c.relocs). Position-independent encodings that need no dynamic relocation (for example PC-relative offsets, matching the !C->needsDynamicRelocation() case quoted in the prior art) have no counterpart in c.relocs, so they are outside this result.
* With link-time-resolved addresses (no dynamic relocation) a .rodata slot loads: see the positive control linkResolved_rodata_loadOk_writeFaultsAfter_and_image. In that theorem the load-time symbol table saR is arbitrary: linkResolve saL c bakes applyAll saL c.relocs c.init into the image and empties relocs, so loading never reads saR, and the theorem neither checks nor guarantees that load-time addresses agree with saL. Loading a link-resolved image at a different base address without relocation is not modeled.

**Prior art.**

* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), llvm/lib/Target/TargetLoweringObjectFile.cpp lines 297-310 in getKindForGlobal, for a constant whose initializer needs a relocation: the comment at lines 297-299 "In static, ROPI and RWPI relocation models, the linker will resolve all addresses, so the relocation entries will actually be constants by the time the app starts up."; lines 302-306 return SectionKind::getReadOnly() for those relocation models or when !C->needsDynamicRelocation() (line 305); otherwise lines 308-310: "Otherwise, the dynamic linker needs to fix it up, put it in the writable data.rel section." and return SectionKind::getReadOnlyWithRel(); llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp lines 630-631 map ReadOnlyWithRel to the prefix ".data.rel.ro" (".ldata.rel.ro" for large globals). Basis: source. Derived (modeling bridge): the toy's placement classification mirrors this split between constants needing no dynamic relocation and load-time-relocated constants.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1560-1563 (body of the item `relro` / `norelro`, lines 1558-1559; Texinfo markup removed): "Create an ELF PT_GNU_RELRO segment header in the object. This specifies a memory segment that should be made read-only after relocation, if supported. Specifying common-page-size smaller than the system page size will render this protection ineffective." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Where may a pointer-bearing immutable static be placed (.rodata, RELRO, .data) so that the load succeeds and the static is write-protected after entry, and how does that depend on whether addresses are known at link time?

### R2d — `pic_loadOk_and_writeFaultsAfter_iff_relro`

**Plain claim.** Let r be a dynamic relocation of loader input c (r ∈ c.relocs) such that every other relocation of c whose slot differs from r's writes a mapped-writable slot, and let protect cover every RELRO byte (H3) and no mutable byte (H4). Then, for every symbol table sa, the two-phase load succeeds and r's slot has post-entry write protection iff r's slot is a RELRO byte.

**Kind / tier / depth.** characterization / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results.lean:169-174
theorem pic_loadOk_and_writeFaultsAfter_iff_relro (c : Cfg) (sa : SymTab) (r : Reloc)
    (hr : r ∈ c.relocs)
    (hOthers : ∀ r' ∈ c.relocs, r'.slot ≠ r.slot → mapWr c.kinds r'.slot = true)
    (hCover : ProtCoversRelro c) (hAvoid : ProtAvoidsMut c) :
    (LoadOk (trace c sa (twoPhase c [])) ∧ WriteFaultsAfter c sa r.slot) ↔
      c.kinds[r.slot]? = some .relro := by
```

Unfolded (prose): by `writeFaultsAfter_iff`, `WriteFaultsAfter c sa a` holds iff `(mapWr c.kinds a && !c.prot a) = false`, that is, iff `a` is not writable after `protect`; by `loadOk_twoPhase_iff`, the load succeeds iff `RelocSlotsWritable c`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hr : r ∈ c.relocs` | r is applied at load time | tight: `placement_iff_cex_not_dynamic` (witness class: a one-byte toy image after link-time resolution) |
| `hOthers : ∀ r' ∈ c.relocs, r'.slot ≠ r.slot → mapWr c.kinds r'.slot = true` | a fault caused by an unrelated relocation would make the load fail whatever r's placement | tight: `placement_iff_cex_other_reloc` (witness class: a toy loader input with at most two bytes and at most two relocations) |
| `hCover : ProtCoversRelro c` | RELRO bytes are protected | tight: `placement_iff_cex_no_cover` (witness class: a toy loader input with at most two bytes and at most two relocations) |
| `hAvoid : ProtAvoidsMut c` | mutable bytes are not protected; without it a covered .data slot also qualifies | tight: `placement_iff_cex_cover_mut` (witness class: a toy loader input with at most two bytes and at most two relocations) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** goodCfg with r = symReloc 0 0 (slot 0, RELRO) satisfies all four hypotheses (third conjunct of placement_nonvacuity); here both sides hold. (`placement_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* "RELRO" in this card is the toy kind relro together with H3 and H4; the equivalence is relative to those assumptions about protect, not a statement about which ELF sections a real linker protects.
* Under link-time-resolved addresses the classification changes (.rodata loads: linkResolved_rodata_loadOk_writeFaultsAfter_and_image); the card applies to relocations applied by the loader.
* This applies to slots written by a dynamic relocation (r ∈ c.relocs). Position-independent encodings that need no dynamic relocation (for example PC-relative offsets, matching the !C->needsDynamicRelocation() case quoted in the prior art) have no counterpart in c.relocs, so they are outside this result.
* The one-directional auxiliary lemmas pic_data_slot_loads_and_write_succeeds (mutable slot: load succeeds, later writes succeed; hypotheses H1, H4) and pic_relro_slot_loads_and_writeFaultsAfter (RELRO slot: load succeeds, writes fault; hypotheses H1, H3) are stated for a relocated slot r.slot with r ∈ c.relocs. That membership restricts the statements to relocated slots and is harmless: their conclusions hold for every byte of the given kind (the proofs do not use it).

**Prior art.**

* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), llvm/lib/Target/TargetLoweringObjectFile.cpp lines 297-310 in getKindForGlobal, for a constant whose initializer needs a relocation: the comment at lines 297-299 "In static, ROPI and RWPI relocation models, the linker will resolve all addresses, so the relocation entries will actually be constants by the time the app starts up."; lines 302-306 return SectionKind::getReadOnly() for those relocation models or when !C->needsDynamicRelocation() (line 305); otherwise lines 308-310: "Otherwise, the dynamic linker needs to fix it up, put it in the writable data.rel section." and return SectionKind::getReadOnlyWithRel(); llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp lines 630-631 map ReadOnlyWithRel to the prefix ".data.rel.ro" (".ldata.rel.ro" for large globals). Basis: source. Derived (modeling bridge): the toy's placement classification mirrors this split between constants needing no dynamic relocation and load-time-relocated constants.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1560-1563 (body of the item `relro` / `norelro`, lines 1558-1559; Texinfo markup removed): "Create an ELF PT_GNU_RELRO segment header in the object. This specifies a memory segment that should be made read-only after relocation, if supported. Specifying common-page-size smaller than the system page size will render this protection ineffective." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Where may a pointer-bearing immutable static be placed (.rodata, RELRO, .data) so that the load succeeds and the static is write-protected after entry, and how does that depend on whether addresses are known at link time?

### R3a — `lazyBound_not_callWorks_and_writeFaultsAfter`

**Plain claim.** For every loader input c (any layout, any protected range), symbol table sa, and slot x lazily bound to symbol t (x is listed as lazy with target t, initially holds the resolver stub, and no dynamic relocation writes it), it is not the case that both the call through x works (CallWorks: the one-operation program [call x], run as the sole program operation immediately after entry, loads without fault and jumps to t's address) and x has post-entry write protection.

**Kind / tier / depth.** impossibility / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness, counterexample and positive control named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results.lean:217-218
theorem lazyBound_not_callWorks_and_writeFaultsAfter (c : Cfg) (sa : SymTab) (x : Nat) (t : Sym)
    (h : LazyBound c x t) : ¬ (CallWorks c sa x t ∧ WriteFaultsAfter c sa x) := by
```

Unfolded (prose): `CallWorks c sa x t` says that for the timeline `twoPhase c [.call x]` no relocation faults and the program outcomes are exactly `[.jump (sa t)]`; `WriteFaultsAfter c sa x` says that after every program prefix `ops`, a further write of any value to `x` faults.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : LazyBound c x t` | the slot is bound by a write at its first use after entry | tight: `eager_relro_callWorks_and_writeFaultsAfter` (witness class: a one-byte toy image with an eagerly bound RELRO slot) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** lazyRelroCfg: slot 0 lazily bound and placed inside the protected range (it is write-protected and the one-operation program [call 0] faults), lazy_inside_protect_writeFaultsAfter_first_call_faults; lazyMutCfg: slot 0 lazily bound outside it (the one-operation program [call 0] works and a write succeeds), partial_relro_lazy_slot_write_redirects_call. (`lazy_inside_protect_writeFaultsAfter_first_call_faults`)

**Positive control.** eagerCfg: slot 0 is not lazily bound (it is eagerly bound in RELRO); its call works and it has post-entry write protection. (`eager_relro_callWorks_and_writeFaultsAfter`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It does not say lazy binding is insecure in every threat model; integrity here is the toy's per-write faulting, and the attacker is arbitrary program writes after entry.
* CallWorks checks the isolated one-operation program [call x] executed immediately at entry, with no preceding program operation; later calls, re-binding and multi-operation programs are not covered.
* Escape hatches not ruled out by this impossibility, none of which the toy models: (a) a loader that changes permissions around each lazy binding; (b) hardware privilege or protection-domain separation giving the resolver write access that ordinary program writes lack; (c) non-caching lazy resolution that resolves the target on each call without writing x. The toy's resolver writes x with the program's own permissions.
* This impossibility concerns one lazily bound slot. It does not say that partial RELRO leaves eagerly bound slots (such as non-PLT GOT entries or .data.rel.ro) unprotected.

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1479-1482 (body of the item `lazy`, line 1478): "When generating an executable or shared library, mark it to tell the dynamic linker to defer function call resolution to the point when the function is called (lazy binding), rather than at load time. Lazy binding is the default."; lines 1538-1542 (body of the item `now`, line 1537): "When generating an executable or shared library, mark it to tell the dynamic linker to resolve all symbols when the program is started, or when the shared library is loaded by dlopen, instead of deferring function call resolution to the point when the function is first called." Basis: documentation.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ld.lld.1 lines 853-858 (item norelro; mdoc markup removed): "Do not indicate that portions of the object should be mapped read-only after initial relocation processing. The object will omit the PT_GNU_RELRO segment."; lines 867-872 (item now): "Set the DF_BIND_NOW flag to indicate that the run-time loader should perform all relocation processing as part of object initialization. By default relocations may be performed on demand." Basis: documentation.
* Background: F. Song (MaskRay), "All about Global Offset Table", 2021-08-29 (updated 2025-05), https://maskray.me/blog/2021-08-29-all-about-global-offset-table (living document, snapshot 2026-11-21, lines 704-706 and 708-710): "With -z relro, the linker places .got into PT_GNU_RELRO. At runtime, after ld.so resolved relocations for an object, it calls mprotect(relro_start, relro_size, PROT_READ) to mark the .got region read-only. This is sometimes called "partial RELRO"." and "With -z relro -z now, the linker additionally places .got.plt into PT_GNU_RELRO. At runtime, ld.so resolves .got.plt relocations eagerly and then calls mprotect. This scheme disables lazy binding PLT. It is sometimes called "full RELRO"." Basis: documentation (practitioner write-up).

**Basis (real systems).** derived (modeling bridge): the toy's eager and lazy binding stand for the documented `-z now` and `-z lazy` (GNU ld) and `DF_BIND_NOW` (lld) behaviour quoted under Prior art, and the practitioner description of partial and full RELRO; that correspondence rests on this documentation, not on the Lean proof, and no loader implementation was examined for this card.

**Design question.** What can RELRO guarantee for binding (GOT/PLT-like) slots under eager versus lazy binding?

### R3b — `bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks`

**Plain claim.** For every loader input c, symbol table sa and list B of bindings (x, t): if every binding in B is either eagerly bound with x a RELRO byte or lazily bound (with x anywhere), the call through every binding slot in B works (CallWorks c sa x t: the one-operation program [call x], run as the sole program operation immediately after entry, loads without fault and jumps to t's address), and protect covers every RELRO byte (H3), then every binding slot in B has post-entry write protection iff every binding in B is eagerly bound.

**Kind / tier / depth.** characterization / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results.lean:250-253
theorem bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks (c : Cfg)
    (sa : SymTab) (B : List (Nat × Sym)) (hPl : EagerRelroOrLazy c B)
    (hCalls : ∀ b ∈ B, CallWorks c sa b.1 b.2) (hCover : ProtCoversRelro c) :
    (∀ b ∈ B, WriteFaultsAfter c sa b.1) ↔ (∀ b ∈ B, EagerBound c b.1 b.2) := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hPl : EagerRelroOrLazy c B` | eager slots sit in RELRO; lazy slots may sit anywhere | tight: `bindings_iff_cex_eager_outside_relro` (witness class: a one-byte toy image with an eager slot in unprotected mutable data) |
| `hCalls : ∀ b ∈ B, CallWorks c sa b.1 b.2` | the bindings function; the forward direction uses it through the lazy-binding impossibility | tight: `bindings_iff_cex_call_faults` (witness class: a one-byte toy image with a lazy slot inside the protected range) |
| `hCover : ProtCoversRelro c` | RELRO bytes are protected (used by the backward direction) | tight: `bindings_iff_cex_no_cover` (witness class: a one-byte toy image with an eager RELRO slot and an empty protected range) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** mixedCfg with B = [(0, 0), (1, 1)]: slot 0 eager in RELRO, slot 1 lazy in mutable data; the placement, the calls (via bindings_callWorks_of_eagerRelroOrLazyMut) and H3 hold (bindings_nonvacuity). Both sides of the equivalence are false there, as slot 1 is lazy. (`bindings_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The forward direction (protection implies eager) goes through the lazy-binding semantics, by lazyBound_not_callWorks_and_writeFaultsAfter; it uses no placement of lazy slots and no hypothesis that protect avoids mutable bytes. The backward direction uses the RELRO placement of eager slots and H3.
* For a list B that mixes eager and lazy bindings, both sides are false. This does not mean that the eager slots of B lose protection: for an eager binding b of B, the theorem applied to the singleton list [b] (whose hypotheses follow from those for B) gives post-entry write protection of b's slot.
* CallWorks checks the isolated one-operation program [call x] executed immediately at entry; in a multi-operation program an earlier write to a writable lazy slot can redirect even the first call through it (partial_relro_lazy_slot_write_redirects_call).
* It does not state that real linkers use this placement for every binding slot; see the prior-art entries for what is documented.

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1479-1482 (body of the item `lazy`, line 1478): "When generating an executable or shared library, mark it to tell the dynamic linker to defer function call resolution to the point when the function is called (lazy binding), rather than at load time. Lazy binding is the default."; lines 1538-1542 (body of the item `now`, line 1537): "When generating an executable or shared library, mark it to tell the dynamic linker to resolve all symbols when the program is started, or when the shared library is loaded by dlopen, instead of deferring function call resolution to the point when the function is first called." Basis: documentation.
* Background: F. Song (MaskRay), "All about Global Offset Table", 2021-08-29 (updated 2025-05), https://maskray.me/blog/2021-08-29-all-about-global-offset-table (living document, snapshot 2026-11-21, lines 704-706 and 708-710): "With -z relro, the linker places .got into PT_GNU_RELRO. At runtime, after ld.so resolved relocations for an object, it calls mprotect(relro_start, relro_size, PROT_READ) to mark the .got region read-only. This is sometimes called "partial RELRO"." and "With -z relro -z now, the linker additionally places .got.plt into PT_GNU_RELRO. At runtime, ld.so resolves .got.plt relocations eagerly and then calls mprotect. This scheme disables lazy binding PLT. It is sometimes called "full RELRO"." Basis: documentation (practitioner write-up).
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ld.lld.1 lines 853-858 (item norelro; mdoc markup removed): "Do not indicate that portions of the object should be mapped read-only after initial relocation processing. The object will omit the PT_GNU_RELRO segment."; lines 867-872 (item now): "Set the DF_BIND_NOW flag to indicate that the run-time loader should perform all relocation processing as part of object initialization. By default relocations may be performed on demand." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): the toy's eager and lazy binding stand for the documented `-z now` and `-z lazy` (GNU ld) and `DF_BIND_NOW` (lld) behaviour quoted under Prior art, and the practitioner description of partial and full RELRO; that correspondence rests on this documentation, not on the Lean proof, and no loader implementation was examined for this card.

**Design question.** What can RELRO guarantee for binding (GOT/PLT-like) slots under eager versus lazy binding?

### R3c — `bindings_callWorks_of_eagerRelroOrLazyMut`

**Plain claim.** For every loader input c, symbol table sa and list B of bindings (x, t): if every binding in B is eagerly bound with x a RELRO byte or lazily bound with x a mutable byte, every relocated slot is mapped writable (H1), and protect covers no mutable byte (H4), then for every binding (x, t) in B the one-operation program [call x], run as the sole program operation immediately after entry, loads without fault and jumps to t's address (CallWorks).

**Kind / tier / depth.** theorem / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results.lean:271-274
theorem bindings_callWorks_of_eagerRelroOrLazyMut (c : Cfg) (sa : SymTab)
    (B : List (Nat × Sym)) (hPl : EagerRelroOrLazyMut c B)
    (hWr : RelocSlotsWritable c) (hAvoid : ProtAvoidsMut c) :
    ∀ b ∈ B, CallWorks c sa b.1 b.2 := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hPl : EagerRelroOrLazyMut c B` | canonical placement: eager slots in RELRO, lazy slots in writable data | tight: `callWorks_cex_lazy_in_relro` (witness class: a one-byte toy image with a lazy slot inside the protected range) |
| `hWr : RelocSlotsWritable c` | the load does not fault | tight: `callWorks_cex_slot_not_writable` (witness class: a toy loader input with at most two bytes and at most two relocations) |
| `hAvoid : ProtAvoidsMut c` | lazy slots stay writable for the binding write | tight: `callWorks_cex_cover_mut` (witness class: a one-byte toy image with a protected lazy mutable slot) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** mixedCfg with B = [(0, 0), (1, 1)] satisfies the placement, H1 and H4 (bindings_callWorks_nonvacuity). (`bindings_callWorks_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* CallWorks checks the isolated one-operation program [call x] executed immediately at entry, with no preceding program operation; later calls are not covered. In a multi-operation program an earlier write to a writable lazy slot overwrites the stub and redirects even the first call through that slot: partial_relro_lazy_slot_write_redirects_call (a write of 55 followed by a call jumps to 55).
* It states that the calls work, not that the slots are protected; under the same placement the lazy slots stay writable (R3b, R3a).

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1479-1482 (body of the item `lazy`, line 1478): "When generating an executable or shared library, mark it to tell the dynamic linker to defer function call resolution to the point when the function is called (lazy binding), rather than at load time. Lazy binding is the default."; lines 1538-1542 (body of the item `now`, line 1537): "When generating an executable or shared library, mark it to tell the dynamic linker to resolve all symbols when the program is started, or when the shared library is loaded by dlopen, instead of deferring function call resolution to the point when the function is first called." Basis: documentation.
* Background: F. Song (MaskRay), "All about Global Offset Table", 2021-08-29 (updated 2025-05), https://maskray.me/blog/2021-08-29-all-about-global-offset-table (living document, snapshot 2026-11-21, lines 704-706 and 708-710): "With -z relro, the linker places .got into PT_GNU_RELRO. At runtime, after ld.so resolved relocations for an object, it calls mprotect(relro_start, relro_size, PROT_READ) to mark the .got region read-only. This is sometimes called "partial RELRO"." and "With -z relro -z now, the linker additionally places .got.plt into PT_GNU_RELRO. At runtime, ld.so resolves .got.plt relocations eagerly and then calls mprotect. This scheme disables lazy binding PLT. It is sometimes called "full RELRO"." Basis: documentation (practitioner write-up).

**Basis (real systems).** derived (modeling bridge): the toy's eager and lazy binding stand for the documented `-z now` and `-z lazy` (GNU ld) behaviour quoted under Prior art, and the practitioner description of partial and full RELRO; that correspondence rests on this documentation, not on the Lean proof, and no loader implementation was examined for this card.

**Design question.** What can RELRO guarantee for binding (GOT/PLT-like) slots under eager versus lazy binding?

### R4a — `downDown_avoidsMut_of_firstPage_noMut`

**Plain claim.** For every page size P and layout L, if the RELRO bytes of L are exactly the range [rs, re) (rs ≤ re ≤ L.length) and no mutable byte lies in [alignDown P rs, rs) (the bytes of the page of address rs below rs, where alignDown P a = a / P * P uses floor division; for P > 0 this range is empty when rs % P = 0, for P = 0 it is [0, rs) because floor division by zero gives alignDown 0 rs = 0, and it is defined also for an empty RELRO range rs = re), then the down-down mask [alignDown P rs, alignDown P re) covers no mutable byte.

**Kind / tier / depth.** theorem / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:73-75
theorem downDown_avoidsMut_of_firstPage_noMut (P rs re : Nat) (L : List Kind)
    (hR : RelroIs L rs re) (hFirst : NoMutIn L (alignDown P rs) rs) :
    AvoidsMut L (roundedMask .downDown P rs re) := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hR : RelroIs L rs re` | the RELRO bytes form exactly the range [rs, re) inside the image | tight: `downDown_avoidsMut_cex_relroIs` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |
| `hFirst : NoMutIn L (alignDown P rs) rs` | start-of-region condition: rounding the start down covers these bytes | tight: `downDown_avoidsMut_cex_firstPage` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** RELRO [0, 2) over [relro, relro, mutable] with P = 2 satisfies both hypotheses (pageRounding_nonvacuity). (`pageRounding_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Without the first-page condition the down-down mask can cover a mutable byte below the RELRO start: downDown_avoidsMut_cex_firstPage, and concretely endAligned_firstPage_mut_no_pageGranular_protection, where a program write to that byte faults. The statement "down-down never faults a legal write" is false in this toy without that condition.
* It does not say that down-down covers all RELRO bytes (for non-empty RELRO rs < re, coverage holds iff re % P = 0: R4b).
* For P = 0, floor division gives alignDown 0 a = 0, so the mask is empty and the conclusion holds trivially; this edge carries no information.
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**Prior art.**

* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/dl-reloc.c lines 353-370, function _dl_protect_relro (paraphrase of the source): start = ALIGN_DOWN(l_addr + l_relro_addr, pagesize), end = ALIGN_DOWN(l_addr + l_relro_addr + l_relro_size, pagesize), and __mprotect(start, end - start, PROT_READ) is called only if start != end; line 301 of _dl_relocate_object calls ELF_DYNAMIC_RELOCATE, and lines 348-349 then run "if (l->l_relro_size != 0)" / "_dl_protect_relro (l);". Basis: source. Derived (modeling bridge): the toy's down-down policy has the same rounding shape (both ends rounded down), and the toy's two-phase timeline has the same relocate-then-protect order for one object. The protection requested is PROT_READ, which also withholds execute permission; the toy tracks write permission alone.
* musl 1.2.5 (upstream repository https://git.musl-libc.org/git/musl, tag v1.2.5, commit 0784374d561435f7c787a555aeab8ede699ed298; ldso/dynlink.c at that revision is git blob 324aa85919f0fdef3156ec36774be2c55ba1d3a4), ldso/dynlink.c lines 734-735: "dso->relro_start = ph->p_vaddr & -PAGE_SIZE;" / "dso->relro_end = (ph->p_vaddr + ph->p_memsz) & -PAGE_SIZE;"; lines 1425-1427 call mprotect with PROT_READ on [relro_start, relro_end) (relative to the object's load base) under the condition on line 1425, "head != &ldso && p->relro_start != p->relro_end". Basis: source. Derived (modeling bridge): the same down-down rounding shape as the toy's downDown policy.
* FreeBSD (freebsd/freebsd-src, branch releng/14.1 at commit f389e68ca980b7e053a34d9eddde89b4c2a1ee6c), libexec/rtld-elf/rtld.c lines 1701-1703 (digest_phdr): "obj->relro_page = obj->relocbase + rtld_trunc_page(ph->p_vaddr);" / "obj->relro_size = rtld_trunc_page(ph->p_vaddr + ph->p_memsz) -" / "rtld_trunc_page(ph->p_vaddr);". Basis: source. Derived (modeling bridge): the same down-down rounding shape for the objects this code path handles; other code paths (lines 2395-2397, for the dynamic linker's own image) compute the size differently and are not modeled.
* Android Bionic (aosp-mirror/platform_bionic, branch android14-release at commit e4df46f213d8d363017dce7ded5d1f2159614425), linker/linker_phdr.cpp lines 899-901 (comment markers removed): "Tricky: what happens when the relro segment does not start or end at page boundaries? We're going to be over-protective here and put every page touched by the segment as read-only."; lines 915-916 (code): "ElfW(Addr) seg_page_start = PAGE_START(phdr->p_vaddr) + load_bias;" / "ElfW(Addr) seg_page_end   = PAGE_END(phdr->p_vaddr + phdr->p_memsz) + load_bias;"; lines 907-914 quote a description attributed to Ian Lance Taylor (the original post was not retrieved): "Note that the current dynamic linker code will only work correctly if the PT_GNU_RELRO segment starts on a page boundary. This is because the dynamic linker rounds the p_vaddr field down to the previous page boundary. If there is anything on the page which should not be read-only, the program is likely to fail at runtime. So in effect the linker must only emit a PT_GNU_RELRO segment if it ensures that it starts on a page boundary." Basis: source. Derived (modeling bridge): the toy's down-up policy has the same rounding shape (start rounded down, end rounded up), and the quoted description is the start-of-region condition of R4a, R4d and R4g.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/ELF/Writer.cpp lines 667-668 (comment in getSectionRank; comment markers removed): "The layout for writable sections is PT_LOAD(PT_GNU_RELRO(.data.rel.ro .bss.rel.ro) | .data .bss), where | marks where page alignment happens." Basis: source comment. Derived (modeling bridge): with RELRO at the start of a page-aligned writable segment, the bytes of the first RELRO page below the RELRO start are not writable data of that segment, which is the situation in which the first-page condition of R4a, R4d and R4g holds.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1560-1563 (body of the item `relro` / `norelro`, lines 1558-1559; Texinfo markup removed): "Create an ELF PT_GNU_RELRO segment header in the object. This specifies a memory segment that should be made read-only after relocation, if supported. Specifying common-page-size smaller than the system page size will render this protection ineffective." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Under page-granular protection, which layouts admit RELRO protection with no spurious fault on mutable data, and what do the down-down and down-up rounding policies guarantee?

### R4b — `downDown_coversRelro_iff_end_aligned`

**Plain claim.** For every page size P and layout L, if the RELRO bytes of L are exactly the non-empty range [rs, re) (rs < re), then the down-down mask [alignDown P rs, alignDown P re) (ends rounded down by floor division) covers every RELRO byte iff re % P = 0 (Nat modulo, with re % 0 = re; for P = 0 both sides are false).

**Kind / tier / depth.** characterization / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:91-93
theorem downDown_coversRelro_iff_end_aligned (P rs re : Nat) (L : List Kind)
    (hR : RelroIs L rs re) (hne : rs < re) :
    CoversRelro L (roundedMask .downDown P rs re) ↔ re % P = 0 := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hR : RelroIs L rs re` | the RELRO bytes form exactly [rs, re) | tight: `downDown_coversRelro_iff_cex_relroIs` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |
| `hne : rs < re` | for an empty RELRO range the mask trivially covers all (zero) RELRO bytes | tight: `downDown_coversRelro_iff_cex_empty` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** RELRO [0, 2) over [relro, relro, mutable] with P = 2 satisfies both hypotheses (pageRounding_nonvacuity; aligned end, both sides true); downDown_unpaddedEnd_tail_write_succeeds is an instance with both sides false, where a program write to the uncovered RELRO byte 2 succeeds. (`pageRounding_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It is about the down-down mask alone; whether a real linker pads the RELRO end to a page boundary is not examined here (the GNU ld documentation of DATA_SEGMENT_RELRO_END and its common-page-size warning are quoted in the prior art).
* Down-down rounding of the start is covered by R4a (start-of-region condition).
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**Prior art.**

* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/dl-reloc.c lines 353-370, function _dl_protect_relro (paraphrase of the source): start = ALIGN_DOWN(l_addr + l_relro_addr, pagesize), end = ALIGN_DOWN(l_addr + l_relro_addr + l_relro_size, pagesize), and __mprotect(start, end - start, PROT_READ) is called only if start != end; line 301 of _dl_relocate_object calls ELF_DYNAMIC_RELOCATE, and lines 348-349 then run "if (l->l_relro_size != 0)" / "_dl_protect_relro (l);". Basis: source. Derived (modeling bridge): the toy's down-down policy has the same rounding shape (both ends rounded down), and the toy's two-phase timeline has the same relocate-then-protect order for one object. The protection requested is PROT_READ, which also withholds execute permission; the toy tracks write permission alone.
* musl 1.2.5 (upstream repository https://git.musl-libc.org/git/musl, tag v1.2.5, commit 0784374d561435f7c787a555aeab8ede699ed298; ldso/dynlink.c at that revision is git blob 324aa85919f0fdef3156ec36774be2c55ba1d3a4), ldso/dynlink.c lines 734-735: "dso->relro_start = ph->p_vaddr & -PAGE_SIZE;" / "dso->relro_end = (ph->p_vaddr + ph->p_memsz) & -PAGE_SIZE;"; lines 1425-1427 call mprotect with PROT_READ on [relro_start, relro_end) (relative to the object's load base) under the condition on line 1425, "head != &ldso && p->relro_start != p->relro_end". Basis: source. Derived (modeling bridge): the same down-down rounding shape as the toy's downDown policy.
* FreeBSD (freebsd/freebsd-src, branch releng/14.1 at commit f389e68ca980b7e053a34d9eddde89b4c2a1ee6c), libexec/rtld-elf/rtld.c lines 1701-1703 (digest_phdr): "obj->relro_page = obj->relocbase + rtld_trunc_page(ph->p_vaddr);" / "obj->relro_size = rtld_trunc_page(ph->p_vaddr + ph->p_memsz) -" / "rtld_trunc_page(ph->p_vaddr);". Basis: source. Derived (modeling bridge): the same down-down rounding shape for the objects this code path handles; other code paths (lines 2395-2397, for the dynamic linker's own image) compute the size differently and are not modeled.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 7326-7335 (item DATA_SEGMENT_RELRO_END(offset, exp), lines 7324-7325; Texinfo markup removed): "This defines the end of the PT_GNU_RELRO segment when -z relro option is used. When -z relro option is not present, DATA_SEGMENT_RELRO_END does nothing, otherwise DATA_SEGMENT_ALIGN is padded so that exp + offset is aligned to the commonpagesize argument given to DATA_SEGMENT_ALIGN. If present in the linker script, it must be placed between DATA_SEGMENT_ALIGN and DATA_SEGMENT_END. Evaluates to the second argument plus any padding needed at the end of the PT_GNU_RELRO segment due to section alignment." Basis: documentation. Derived (modeling bridge): padding the RELRO end to a page boundary is the layout condition re % P = 0 of R4b, with commonpagesize in the role of P.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1560-1563 (body of the item `relro` / `norelro`, lines 1558-1559; Texinfo markup removed): "Create an ELF PT_GNU_RELRO segment header in the object. This specifies a memory segment that should be made read-only after relocation, if supported. Specifying common-page-size smaller than the system page size will render this protection ineffective." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Under page-granular protection, which layouts admit RELRO protection with no spurious fault on mutable data, and what do the down-down and down-up rounding policies guarantee?

### R4c — `downUp_coversRelro`

**Plain claim.** For every page size P > 0 and layout L, if the RELRO bytes of L are exactly [rs, re), then the down-up mask covers every RELRO byte. For rs < re the down-up mask is [alignDown P rs, alignUp P re), with alignUp P a = (a + P - 1) / P * P (floor division and truncated subtraction); for rs = re there is no RELRO byte and the mask is empty (roundedMask guards the empty range).

**Kind / tier / depth.** theorem / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:119-120
theorem downUp_coversRelro (P rs re : Nat) (L : List Kind) (hP : 0 < P)
    (hR : RelroIs L rs re) : CoversRelro L (roundedMask .downUp P rs re) := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hP : 0 < P` | for P = 0, alignUp 0 a = 0 and the mask is empty | tight: `downUp_coversRelro_cex_pageZero` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |
| `hR : RelroIs L rs re` | the RELRO bytes form exactly [rs, re) | tight: `downUp_coversRelro_cex_relroIs` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** RELRO [0, 2) over [relro, relro, mutable] with P = 2 satisfies both hypotheses (pageRounding_nonvacuity). (`pageRounding_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It does not say the down-up mask avoids mutable bytes (R4d).
* The empty-range guard in roundedMask is a modeling choice: without it, rounding an empty range [rs, rs) with rs % P ≠ 0 outwards would protect the whole page of rs. Whether any real loader receives or protects an empty RELRO range is not examined.
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**Prior art.**

* Android Bionic (aosp-mirror/platform_bionic, branch android14-release at commit e4df46f213d8d363017dce7ded5d1f2159614425), linker/linker_phdr.cpp lines 899-901 (comment markers removed): "Tricky: what happens when the relro segment does not start or end at page boundaries? We're going to be over-protective here and put every page touched by the segment as read-only."; lines 915-916 (code): "ElfW(Addr) seg_page_start = PAGE_START(phdr->p_vaddr) + load_bias;" / "ElfW(Addr) seg_page_end   = PAGE_END(phdr->p_vaddr + phdr->p_memsz) + load_bias;"; lines 907-914 quote a description attributed to Ian Lance Taylor (the original post was not retrieved): "Note that the current dynamic linker code will only work correctly if the PT_GNU_RELRO segment starts on a page boundary. This is because the dynamic linker rounds the p_vaddr field down to the previous page boundary. If there is anything on the page which should not be read-only, the program is likely to fail at runtime. So in effect the linker must only emit a PT_GNU_RELRO segment if it ensures that it starts on a page boundary." Basis: source. Derived (modeling bridge): the toy's down-up policy has the same rounding shape (start rounded down, end rounded up), and the quoted description is the start-of-region condition of R4a, R4d and R4g.
* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/dl-reloc.c lines 353-370, function _dl_protect_relro (paraphrase of the source): start = ALIGN_DOWN(l_addr + l_relro_addr, pagesize), end = ALIGN_DOWN(l_addr + l_relro_addr + l_relro_size, pagesize), and __mprotect(start, end - start, PROT_READ) is called only if start != end; line 301 of _dl_relocate_object calls ELF_DYNAMIC_RELOCATE, and lines 348-349 then run "if (l->l_relro_size != 0)" / "_dl_protect_relro (l);". Basis: source. Derived (modeling bridge): the toy's down-down policy has the same rounding shape (both ends rounded down), and the toy's two-phase timeline has the same relocate-then-protect order for one object. The protection requested is PROT_READ, which also withholds execute permission; the toy tracks write permission alone.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Under page-granular protection, which layouts admit RELRO protection with no spurious fault on mutable data, and what do the down-down and down-up rounding policies guarantee?

### R4d — `downUp_avoidsMut_iff_partialPages_noMut`

**Plain claim.** For every page size P > 0 and layout L, if the RELRO bytes of L are exactly the non-empty range [rs, re) (rs < re), then the down-up mask [alignDown P rs, alignUp P re) covers no mutable byte iff no mutable byte lies in [alignDown P rs, rs) and none lies in [re, alignUp P re) (alignDown P a = a / P * P and alignUp P a = (a + P - 1) / P * P, by floor division and truncated subtraction).

**Kind / tier / depth.** characterization / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:131-134
theorem downUp_avoidsMut_iff_partialPages_noMut (P rs re : Nat) (L : List Kind) (hP : 0 < P)
    (hR : RelroIs L rs re) (hne : rs < re) :
    AvoidsMut L (roundedMask .downUp P rs re) ↔
      NoMutIn L (alignDown P rs) rs ∧ NoMutIn L re (alignUp P re) := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hP : 0 < P` | for P = 0 the mask is empty while the left range [0, rs) can hold mutable bytes | tight: `downUp_avoidsMut_iff_cex_pageZero` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |
| `hR : RelroIs L rs re` | the RELRO bytes form exactly [rs, re) | tight: `downUp_avoidsMut_iff_cex_relroIs` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |
| `hne : rs < re` | for an empty range the guarded mask is empty while a mutable byte can lie in [alignDown P rs, rs) | tight: `downUp_avoidsMut_iff_cex_empty` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** RELRO [0, 2) over [relro, relro, mutable] with P = 2 satisfies all three hypotheses (pageRounding_nonvacuity; both sides true); downUp_sharedLastPage_mut_write_faults has both sides false, where a program write to the mutable byte 3 faults. (`pageRounding_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Covering of RELRO bytes by the down-up mask is R4c. Together with R4c, R4g and roundedMask_downUp_pageGranular, the auxiliary lemma downUp_covers_avoids_iff_exists_pageGranular shows: for P > 0 and RELRO bytes exactly a non-empty range [rs, re) (RelroIs L rs re, rs < re), the single interval roundedMask .downUp P rs re covers every RELRO byte and no mutable byte iff some page-granular mask does.
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**Prior art.**

* Android Bionic (aosp-mirror/platform_bionic, branch android14-release at commit e4df46f213d8d363017dce7ded5d1f2159614425), linker/linker_phdr.cpp lines 899-901 (comment markers removed): "Tricky: what happens when the relro segment does not start or end at page boundaries? We're going to be over-protective here and put every page touched by the segment as read-only."; lines 915-916 (code): "ElfW(Addr) seg_page_start = PAGE_START(phdr->p_vaddr) + load_bias;" / "ElfW(Addr) seg_page_end   = PAGE_END(phdr->p_vaddr + phdr->p_memsz) + load_bias;"; lines 907-914 quote a description attributed to Ian Lance Taylor (the original post was not retrieved): "Note that the current dynamic linker code will only work correctly if the PT_GNU_RELRO segment starts on a page boundary. This is because the dynamic linker rounds the p_vaddr field down to the previous page boundary. If there is anything on the page which should not be read-only, the program is likely to fail at runtime. So in effect the linker must only emit a PT_GNU_RELRO segment if it ensures that it starts on a page boundary." Basis: source. Derived (modeling bridge): the toy's down-up policy has the same rounding shape (start rounded down, end rounded up), and the quoted description is the start-of-region condition of R4a, R4d and R4g.
* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/dl-reloc.c lines 353-370, function _dl_protect_relro (paraphrase of the source): start = ALIGN_DOWN(l_addr + l_relro_addr, pagesize), end = ALIGN_DOWN(l_addr + l_relro_addr + l_relro_size, pagesize), and __mprotect(start, end - start, PROT_READ) is called only if start != end; line 301 of _dl_relocate_object calls ELF_DYNAMIC_RELOCATE, and lines 348-349 then run "if (l->l_relro_size != 0)" / "_dl_protect_relro (l);". Basis: source. Derived (modeling bridge): the toy's down-down policy has the same rounding shape (both ends rounded down), and the toy's two-phase timeline has the same relocate-then-protect order for one object. The protection requested is PROT_READ, which also withholds execute permission; the toy tracks write permission alone.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/ELF/Writer.cpp lines 667-668 (comment in getSectionRank; comment markers removed): "The layout for writable sections is PT_LOAD(PT_GNU_RELRO(.data.rel.ro .bss.rel.ro) | .data .bss), where | marks where page alignment happens." Basis: source comment. Derived (modeling bridge): with RELRO at the start of a page-aligned writable segment, the bytes of the first RELRO page below the RELRO start are not writable data of that segment, which is the situation in which the first-page condition of R4a, R4d and R4g holds.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Under page-granular protection, which layouts admit RELRO protection with no spurious fault on mutable data, and what do the down-down and down-up rounding policies guarantee?

### R4e — `exists_pageGranular_covers_avoids_iff_noSharedPage`

**Plain claim.** For every layout L and page size P (pages are the classes of equal floor quotient a / P; for P = 0 every address is on page 0), some page-granular mask covers every RELRO byte and no mutable byte iff no page holds both a RELRO byte and a mutable byte.

**Kind / tier / depth.** characterization / T0 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:168-169
theorem exists_pageGranular_covers_avoids_iff_noSharedPage (P : Nat) (L : List Kind) :
    (∃ m, PageGranular P m ∧ CoversRelro L m ∧ AvoidsMut L m) ↔ NoSharedPage P L := by
```

**Hypothesis ledger.**

No side-condition hypotheses (the statement is universally quantified over its arguments).

**Non-vacuity.** No side-condition hypotheses (universally quantified over P : Nat and L : List Kind). noSharedPage_examples: [relro, relro, mutable] with P = 2 (both sides hold); layoutRelro3Mut with P = 2 (both sides fail). (`noSharedPage_examples`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Page-granular masks are arbitrary unions of whole pages, not necessarily one interval. The forward direction transfers to a single protected interval: if some page-granular interval rangeMask lo hi covers RELRO and avoids mutable bytes, then NoSharedPage P L holds, since such an interval is a page-granular mask. The backward direction does not transfer: noncontiguous_relro_noSharedPage_no_single_interval proves that [relro, mutable, relro] with P = 1 satisfies NoSharedPage while no interval [lo, hi) covers both RELRO bytes without the mutable byte. For contiguous non-empty RELRO (RelroIs L rs re, rs < re) and P > 0, the single interval roundedMask .downUp P rs re suffices whenever some page-granular mask does (downUp_covers_avoids_iff_exists_pageGranular).
* Bytes other than RELRO and mutable (code, .rodata) may be covered. The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* This is the separation of two sets by unions of equivalence classes, restated for pages; it is tiered T0.

**Prior art.**

* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/dl-reloc.c lines 353-370, function _dl_protect_relro (paraphrase of the source): start = ALIGN_DOWN(l_addr + l_relro_addr, pagesize), end = ALIGN_DOWN(l_addr + l_relro_addr + l_relro_size, pagesize), and __mprotect(start, end - start, PROT_READ) is called only if start != end; line 301 of _dl_relocate_object calls ELF_DYNAMIC_RELOCATE, and lines 348-349 then run "if (l->l_relro_size != 0)" / "_dl_protect_relro (l);". Basis: source. Derived (modeling bridge): the toy's down-down policy has the same rounding shape (both ends rounded down), and the toy's two-phase timeline has the same relocate-then-protect order for one object. The protection requested is PROT_READ, which also withholds execute permission; the toy tracks write permission alone.
* Android Bionic (aosp-mirror/platform_bionic, branch android14-release at commit e4df46f213d8d363017dce7ded5d1f2159614425), linker/linker_phdr.cpp lines 899-901 (comment markers removed): "Tricky: what happens when the relro segment does not start or end at page boundaries? We're going to be over-protective here and put every page touched by the segment as read-only."; lines 915-916 (code): "ElfW(Addr) seg_page_start = PAGE_START(phdr->p_vaddr) + load_bias;" / "ElfW(Addr) seg_page_end   = PAGE_END(phdr->p_vaddr + phdr->p_memsz) + load_bias;"; lines 907-914 quote a description attributed to Ian Lance Taylor (the original post was not retrieved): "Note that the current dynamic linker code will only work correctly if the PT_GNU_RELRO segment starts on a page boundary. This is because the dynamic linker rounds the p_vaddr field down to the previous page boundary. If there is anything on the page which should not be read-only, the program is likely to fail at runtime. So in effect the linker must only emit a PT_GNU_RELRO segment if it ensures that it starts on a page boundary." Basis: source. Derived (modeling bridge): the toy's down-up policy has the same rounding shape (start rounded down, end rounded up), and the quoted description is the start-of-region condition of R4a, R4d and R4g.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1560-1563 (body of the item `relro` / `norelro`, lines 1558-1559; Texinfo markup removed): "Create an ELF PT_GNU_RELRO segment header in the object. This specifies a memory segment that should be made read-only after relocation, if supported. Specifying common-page-size smaller than the system page size will render this protection ineffective." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Under page-granular protection, which layouts admit RELRO protection with no spurious fault on mutable data, and what do the down-down and down-up rounding policies guarantee?

### R4g — `exists_pageGranular_covers_avoids_iff_partialPages_noMut`

**Plain claim.** For every page size P > 0 and layout L whose RELRO bytes are exactly the non-empty range [rs, re) (rs < re): some page-granular mask covers every RELRO byte and no mutable byte iff no mutable byte lies in [alignDown P rs, rs) and none lies in [re, alignUp P re) (alignDown and alignUp by floor division and truncated subtraction). When re % P = 0 the second range is empty (alignUp_eq_self_of_mod_eq_zero).

**Kind / tier / depth.** characterization / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:221-224
theorem exists_pageGranular_covers_avoids_iff_partialPages_noMut (P rs re : Nat) (L : List Kind)
    (hP : 0 < P) (hR : RelroIs L rs re) (hne : rs < re) :
    (∃ m, PageGranular P m ∧ CoversRelro L m ∧ AvoidsMut L m) ↔
      NoMutIn L (alignDown P rs) rs ∧ NoMutIn L re (alignUp P re) :=
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hP : 0 < P` | for P = 0 every address is on page 0 | tight: `exists_pageGranular_iff_cex_pageZero` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |
| `hR : RelroIs L rs re` | the RELRO bytes form exactly [rs, re) | tight: `exists_pageGranular_iff_cex_relroIs` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |
| `hne : rs < re` | non-empty RELRO | tight: `exists_pageGranular_iff_cex_empty` (witness class: a toy layout of at most four bytes with page size 0, 1 or 2) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** RELRO [0, 2) over [relro, relro, mutable] with P = 2 satisfies all three hypotheses (pageRounding_nonvacuity). (`pageRounding_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The condition has two parts. "RELRO end aligned, or the shared last page holds no mutable data" is not sufficient: endAligned_firstPage_mut_no_pageGranular_protection has an aligned end and a clean last page, but a mutable byte on the first RELRO page, and no page-granular protection exists.
* Whether real linkers ever place mutable data on the first RELRO page below the RELRO start is not examined here; the prior art quotes documentation describing that hazard and a linker layout that places RELRO at the start of a writable segment.
* The proof composes R4e with the auxiliary interval lemma noSharedPage_iff_partialPages_noMut (same hypotheses).
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**Prior art.**

* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/dl-reloc.c lines 353-370, function _dl_protect_relro (paraphrase of the source): start = ALIGN_DOWN(l_addr + l_relro_addr, pagesize), end = ALIGN_DOWN(l_addr + l_relro_addr + l_relro_size, pagesize), and __mprotect(start, end - start, PROT_READ) is called only if start != end; line 301 of _dl_relocate_object calls ELF_DYNAMIC_RELOCATE, and lines 348-349 then run "if (l->l_relro_size != 0)" / "_dl_protect_relro (l);". Basis: source. Derived (modeling bridge): the toy's down-down policy has the same rounding shape (both ends rounded down), and the toy's two-phase timeline has the same relocate-then-protect order for one object. The protection requested is PROT_READ, which also withholds execute permission; the toy tracks write permission alone.
* Android Bionic (aosp-mirror/platform_bionic, branch android14-release at commit e4df46f213d8d363017dce7ded5d1f2159614425), linker/linker_phdr.cpp lines 899-901 (comment markers removed): "Tricky: what happens when the relro segment does not start or end at page boundaries? We're going to be over-protective here and put every page touched by the segment as read-only."; lines 915-916 (code): "ElfW(Addr) seg_page_start = PAGE_START(phdr->p_vaddr) + load_bias;" / "ElfW(Addr) seg_page_end   = PAGE_END(phdr->p_vaddr + phdr->p_memsz) + load_bias;"; lines 907-914 quote a description attributed to Ian Lance Taylor (the original post was not retrieved): "Note that the current dynamic linker code will only work correctly if the PT_GNU_RELRO segment starts on a page boundary. This is because the dynamic linker rounds the p_vaddr field down to the previous page boundary. If there is anything on the page which should not be read-only, the program is likely to fail at runtime. So in effect the linker must only emit a PT_GNU_RELRO segment if it ensures that it starts on a page boundary." Basis: source. Derived (modeling bridge): the toy's down-up policy has the same rounding shape (start rounded down, end rounded up), and the quoted description is the start-of-region condition of R4a, R4d and R4g.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/ELF/Writer.cpp lines 667-668 (comment in getSectionRank; comment markers removed): "The layout for writable sections is PT_LOAD(PT_GNU_RELRO(.data.rel.ro .bss.rel.ro) | .data .bss), where | marks where page alignment happens." Basis: source comment. Derived (modeling bridge): with RELRO at the start of a page-aligned writable segment, the bytes of the first RELRO page below the RELRO start are not writable data of that segment, which is the situation in which the first-page condition of R4a, R4d and R4g holds.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 7326-7335 (item DATA_SEGMENT_RELRO_END(offset, exp), lines 7324-7325; Texinfo markup removed): "This defines the end of the PT_GNU_RELRO segment when -z relro option is used. When -z relro option is not present, DATA_SEGMENT_RELRO_END does nothing, otherwise DATA_SEGMENT_ALIGN is padded so that exp + offset is aligned to the commonpagesize argument given to DATA_SEGMENT_ALIGN. If present in the linker script, it must be placed between DATA_SEGMENT_ALIGN and DATA_SEGMENT_END. Evaluates to the second argument plus any padding needed at the end of the PT_GNU_RELRO segment due to section alignment." Basis: documentation. Derived (modeling bridge): padding the RELRO end to a page boundary is the layout condition re % P = 0 of R4b, with commonpagesize in the role of P.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 1560-1563 (body of the item `relro` / `norelro`, lines 1558-1559; Texinfo markup removed): "Create an ELF PT_GNU_RELRO segment header in the object. This specifies a memory segment that should be made read-only after relocation, if supported. Specifying common-page-size smaller than the system page size will render this protection ineffective." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Under page-granular protection, which layouts admit RELRO protection with no spurious fault on mutable data, and what do the down-down and down-up rounding policies guarantee?

### R5a — `applyAll_perm_of_addressOnly_of_nodup_slots`

**Plain claim.** For every symbol table sa and initial memory m: if every relocation in rs is address-only (its value depends on symbol addresses alone) and the relocations of rs write pairwise distinct slots, then for every order rs' that is a permutation of rs, applying rs' gives the same image as applying rs.

**Kind / tier / depth.** theorem / T0 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:480-482
theorem applyAll_perm_of_addressOnly_of_nodup_slots (sa : SymTab) {rs rs' : List Reloc}
    (p : rs.Perm rs') (hA : ∀ r ∈ rs, r.AddressOnly) (hN : (rs.map Reloc.slot).Nodup)
    (m : Mem) : applyAll sa rs m = applyAll sa rs' m :=
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `p : rs.Perm rs'` | the two orders apply the same relocations | tight: `order_cex_not_perm` (witness class: a one-relocation toy list) |
| `hA : ∀ r ∈ rs, r.AddressOnly` | values do not depend on memory | tight: `resolver_reads_unrelocated_slot_order_dependent` (witness class: a two-relocation toy list) |
| `hN : (rs.map Reloc.slot).Nodup` | two relocations of one slot: the last one wins | tight: `addressOnly_same_slot_order_dependent` (witness class: a two-relocation toy list) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** [rAddr0, symReloc 2 1] and its reversal satisfy all three hypotheses (addressOnlyOrder_nonvacuity). (`addressOnlyOrder_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It does not assert the order in which any real loader applies relocations, including IFUNC/IRELATIVE relocations.
* Permissions are ignored here (applyAll); with permissions, order also matters if protect is interleaved (R1).
* Relocations whose value reads the slot's previous contents (implicit addends) are not address-only and are outside this result.
* This restates Bernstein-style read/write disjointness for relocations; it is tiered T0.

**Prior art.**

* A. J. Bernstein, "Analysis of Programs for Parallel Processing", IEEE Transactions on Electronic Computers EC-15(5), 1966, pp. 757-763, doi:10.1109/pgec.1966.264565 (bibliographic record verified via Crossref; the paper text was not retrieved). The read-set / write-set disjointness conditions under which two program parts may be executed in either order are known as Bernstein's conditions (as described by secondary summaries). Derived: applyReloc_comm and the permutation results restate such conditions for relocations (each relocation reads its declared read set and writes one slot); this is why the order results are tiered T0.
* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/do-rel.h, function elf_dynamic_do_Rel (paraphrase of the source): the relative relocations, the first nrelative entries of a table, are applied first (lines 123-124); in the main loop entries of type ELF_MACHINE_IRELATIVE are skipped and their span recorded (lines 138-144 and 185-191), and they are applied in a second pass at the end of the same table (lines 164-175 and 211-216). Basis: source. Derived (modeling bridge): within one relocation table, resolver relocations run after the other relocations, as A ++ R does in the toy; ordering across tables and objects is not modeled.
* Background: F. Song (MaskRay), "GNU indirect function", 2021-01-18 (updated 2026-07), https://maskray.me/blog/2021-01-18-gnu-indirect-function (living document, snapshot 2026-11-21): "R_*_GLOB_DAT and R_*_RELATIVE relocations are resolved before R_*_IRELATIVE, so reading a variable or taking an address of a function is fine." Basis: documentation (practitioner write-up).

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** When may a loader model treat relocation application order as irrelevant, and which ordering discipline makes resolver (IFUNC-like) relocations order-independent?

### R5c — `applyAll_append_perm_of_resolvers_read_no_resolver_slot`

**Plain claim.** For every symbol table sa and initial memory m: let A be address-only relocations with pairwise distinct slots, and R resolver relocations with pairwise distinct slots, each of which reads memory only at addresses that no relocation of R writes (it may read any slot of A that no relocation of R writes, and any other memory not written by R). Then for every order produced by permuting A to A' and R to R' and applying all of A' before any of R' (A' ++ R'), the image equals that of A ++ R.

**Kind / tier / depth.** theorem / T0 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:491-495
theorem applyAll_append_perm_of_resolvers_read_no_resolver_slot (sa : SymTab)
    (A R A' R' : List Reloc) (hA : ∀ r ∈ A, r.AddressOnly) (hNA : (A.map Reloc.slot).Nodup)
    (hR : ∀ r ∈ R, r.ReadsOnly (fun a => a ∉ R.map Reloc.slot))
    (hNR : (R.map Reloc.slot).Nodup) (pA : A'.Perm A) (pR : R'.Perm R) (m : Mem) :
    applyAll sa (A' ++ R') m = applyAll sa (A ++ R) m := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hA : ∀ r ∈ A, r.AddressOnly` | the first group is order-independent by itself | tight: `nonAddressOnly_first_group_order_dependent` (witness class: a two-relocation toy list) |
| `hNA : (A.map Reloc.slot).Nodup` | two relocations of one slot in A: the last one wins | tight: `addressOnly_first_group_same_slot_order_dependent` (witness class: a two-relocation toy list) |
| `hR : ∀ r ∈ R, r.ReadsOnly (fun a => a ∉ R.map Reloc.slot)` | no resolver reads a slot that a resolver writes | tight: `resolvers_read_resolver_slot_order_dependent`, `resolver_overwrites_addressOnly_slot_order_dependent` (witness class: toy lists of at most three relocations) |
| `hNR : (R.map Reloc.slot).Nodup` | two resolvers of one slot: the last one wins | tight: `resolvers_same_slot_order_dependent` (witness class: a two-relocation toy list) |
| `pA : A'.Perm A` | A' applies the same relocations as A | tight: `resolverOrder_cex_not_permA` (witness class: a one-relocation toy list) |
| `pR : R'.Perm R` | R' applies the same relocations as R | tight: `resolverOrder_cex_not_permR` (witness class: a one-relocation toy list) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** A = [rAddr0, symReloc 2 1], R = [rRes1, rRes3of2, rRes4of9] (resolvers reading slots 0 and 2 of A and the address 9 that no relocation writes), with A' and R' the reversals, satisfy all six hypotheses (relocationOrder_nonvacuity). (`relocationOrder_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The order family is the one produced by permuting within each group and applying A before R; orders that interleave the groups are not covered (resolver_reads_unrelocated_slot_order_dependent exhibits an interleaved order with a different image).
* It is a sufficient discipline; no necessity is claimed beyond the tightness witnesses listed in the hypothesis ledger.
* Each relocation is modeled as a pure total function of the symbol table and memory that writes one slot and ignores permissions (applyAll). Resolvers with side effects, resolvers that call other resolvers, faulting resolvers, implicit-addend and copy relocations, and dependencies between relocations of different objects are not modeled.
* It does not assert any real loader's ordering of IFUNC/IRELATIVE relocations; the prior art documents the within-table ordering of one loader version.

**Prior art.**

* A. J. Bernstein, "Analysis of Programs for Parallel Processing", IEEE Transactions on Electronic Computers EC-15(5), 1966, pp. 757-763, doi:10.1109/pgec.1966.264565 (bibliographic record verified via Crossref; the paper text was not retrieved). The read-set / write-set disjointness conditions under which two program parts may be executed in either order are known as Bernstein's conditions (as described by secondary summaries). Derived: applyReloc_comm and the permutation results restate such conditions for relocations (each relocation reads its declared read set and writes one slot); this is why the order results are tiered T0.
* glibc 2.40 (tag glibc-2.40, commit 3d1aed874918c466a4477af1da35983ab036690e), elf/do-rel.h, function elf_dynamic_do_Rel (paraphrase of the source): the relative relocations, the first nrelative entries of a table, are applied first (lines 123-124); in the main loop entries of type ELF_MACHINE_IRELATIVE are skipped and their span recorded (lines 138-144 and 185-191), and they are applied in a second pass at the end of the same table (lines 164-175 and 211-216). Basis: source. Derived (modeling bridge): within one relocation table, resolver relocations run after the other relocations, as A ++ R does in the toy; ordering across tables and objects is not modeled.
* Background: F. Song (MaskRay), "GNU indirect function", 2021-01-18 (updated 2026-07), https://maskray.me/blog/2021-01-18-gnu-indirect-function (living document, snapshot 2026-11-21): "R_*_GLOB_DAT and R_*_RELATIVE relocations are resolved before R_*_IRELATIVE, so reading a variable or taking an address of a function is fine." Basis: documentation (practitioner write-up).

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** When may a loader model treat relocation application order as irrelevant, and which ordering discipline makes resolver (IFUNC-like) relocations order-independent?

### R6a — `runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained`

**Plain claim.** For every GC input g, start/stop policy pol and run (a list of section accesses, each an edge access, a bounds access or an implicit access): if (A1) every edge access edge i j follows a relocation edge (i, j) ∈ g.edges from a section i that is a root or was reached by an earlier access of the run, (A2) every implicit access reaches a root, and (A3) every bounds access bounds i X j comes from a section i that references the bounds of X ((i, X) ∈ g.ss) and is a root or was reached earlier, reaches a section j named X, and either the policy is conservative or j is a root, then every section the run accesses is kept by GC (g.Live pol).

**Kind / tier / depth.** theorem / T0 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Gc/Results.lean:89-93
theorem runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained
    (g : GcIn) (pol : SSPolicy) (run : List Acc)
    (h1 : EdgeAccessesFollowEdges g.edges g.IsRoot run)
    (h2 : ImplicitAccessesHitRoots g.IsRoot run)
    (h3 : BoundsAccessesRetained g pol run) : RunPreserved g pol run := by
```

Unfolded (prose): `RunPreserved g pol run` says `∀ a ∈ run, g.Live pol a.dst`, where `g.Live pol` is reachability in the graph `g.edges ++ g.ssEdges pol` from the sections `g.IsRoot`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h1 : EdgeAccessesFollowEdges g.edges g.IsRoot run` | accesses through relocations follow edges the linker sees, from kept sections | tight: `gcSoundness_cex_edge_access_without_edge` (witness class: a toy GC input of at most three sections) |
| `h2 : ImplicitAccessesHitRoots g.IsRoot run` | accesses the linker cannot see target roots | tight: `gcSoundness_cex_implicit_access_to_nonroot` (witness class: a toy GC input of at most three sections) |
| `h3 : BoundsAccessesRetained g pol run` | accesses by iterating __start_X..__stop_X come from kept referencing sections and reach entries that the start/stop rule or a root class retains | tight: `gcSoundness_cex_bounds_access_unretained` (witness class: a toy GC input of at most three sections) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** gcPair [(0, 1)] with the run [implicit 0, edge 0 1] satisfies A1-A3 under either policy (gcSoundness_nonvacuity); gcReg [] false false under the conservative policy with the run [implicit 0, bounds 0 7 1, bounds 0 7 2] satisfies A1-A3 with bounds accesses (gcSoundness_bounds_nonvacuity). (`gcSoundness_nonvacuity`, `gcSoundness_bounds_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Behaviour preservation is modeled as: every accessed section is kept. Address changes caused by removing sections, and code that depends on section sizes or on the absence of sections, are not modeled.
* The access kinds classify how the program obtains an address, so one run is encoded the same way under both policies; the policy enters through A3 alone. A1-A3 are sufficient, not necessary, for one given run: for example, under the precise policy a bounds access to an entry that an earlier edge access reached is kept although A3 fails for it (an example, not proved here). Over all runs they are exact: live_iff_exists_valid_run proves that a section is kept iff some run satisfying A1-A3 accesses it (the converse direction is exists_valid_run_of_live), so the theorem restates reachability-based GC soundness and is tiered T0.
* Edge and reference endpoints are not required to name existing sections: an index past the end of g.secs can be kept along a dangling edge (phantom_section_live).
* The GC graph models relocation edges, four section-level root flags (entry, exported, KEEP, retain) and start/stop references. Static-archive member selection (which happens before section GC), COMDAT groups, SHF_LINK_ORDER dependencies, special-section roots such as init arrays and notes, dummy (R_*_NONE) relocations, /DISCARD/ rules, weak references, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 2030-2039 (Texinfo markup removed): "--gc-sections decides which input sections are used by examining symbols and relocations. The section containing the entry symbol and all sections containing symbols undefined on the command-line will be kept, as will sections containing symbols referenced by dynamic objects. Note that when building shared libraries, the linker must assume that any visible symbol is referenced. Once this initial set of sections has been determined, the linker recursively marks as used any section referenced by their relocations. See --entry, --undefined, and --gc-keep-exported." Basis: documentation. Derived (modeling bridge): the toy's root flags and GcIn.Live (reachability from roots along relocation edges) have this shape.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 5506-5509 (Texinfo markup removed): "If an output section's name is the same as the input section's name and is representable as a C identifier, then the linker will automatically PROVIDE two symbols: __start_SECNAME and __stop_SECNAME, where SECNAME is the name of the section."; lines 5511-5512: "Note: most section names are not representable as C identifiers because they contain a . character."; lines 1595-1602 (item start-stop-gc): "When --gc-sections is in effect, a reference from a retained section to __start_SECNAME or __stop_SECNAME causes all input sections named SECNAME to also be retained, if SECNAME is representable as a C identifier and either __start_SECNAME or __stop_SECNAME is synthesized by the linker. -z start-stop-gc disables this effect, allowing sections to be garbage collected as if the special synthesized symbols were not defined."; lines 1602-1607: "-z start-stop-gc has no effect on a definition of __start_SECNAME or __stop_SECNAME in an object file or linker script. Such a definition will prevent the linker providing a synthesized __start_SECNAME or __stop_SECNAME respectively, and therefore the special treatment by garbage collection for those references."; ld/NEWS lines 142-143 (Changes in 2.37): "Add -z start-stop-gc to disable special treatment of __start_*/__stop_* references when --gc-sections." Basis: documentation. Derived (modeling bridge): the toy's conservative policy mirrors the retaining effect and the precise policy mirrors -z start-stop-gc; the C-identifier condition and user definitions of the bounds are not modeled.
* G. Morrisett, M. Felleisen, R. Harper, "Abstract models of memory management", FPCA 1995, pp. 66-77, doi:10.1145/224164.224182 (bibliographic record verified via Crossref; the paper text was not retrieved): a formal treatment of garbage collection in which, per secondary summaries, collecting unreachable heap objects is shown not to change program results. Derived: R6a restates the reachability-based soundness argument for linker section GC, hence tier T0.
* P. Gammie, A. L. Hosking, K. Engelhardt, "Relaxing safely: verified on-the-fly garbage collection for x86-TSO", PLDI 2015, pp. 99-109, doi:10.1145/2737924.2738006 (bibliographic record verified via Crossref; described by its title): mechanized GC verification, cited as related mechanized work on heap GC, not on linker GC.
* S. Kell, D. P. Mulligan, P. Sewell, "The missing link: explaining ELF static linking, semantically", OOPSLA 2016, pp. 607-623, doi:10.1145/2983990.2983996: a Lem/Isabelle specification of static ELF linking; it states about --gc-sections "we currently do not model it" and restricts itself to static linking (no load-time relocation or RELRO protection).
* Y. Wang, X. Xu, P. Wilke, Z. Shao, "CompCertELF: verified separate compilation of C programs into ELF object files", Proceedings of the ACM on Programming Languages 4 (OOPSLA), 2020, pp. 1-28, doi:10.1145/3428265 (bibliographic record verified via Crossref; described here by its title, the paper text was not re-read for this package). Mechanized ELF object generation and linking; it is cited as related mechanized work, not as covering dynamic loading, RELRO protection or section GC.
* Novelty record: a bounded search (web search and Crossref, 2026-11-21) found the mechanized ELF-linking work of Kell, Mulligan and Sewell (doi:10.1145/2983990.2983996) and CompCertELF (doi:10.1145/3428265); no mechanized model of RELRO page rounding, linker GC retention roots, or compiler-then-linker retention was found. This result is tiered T0 (reachability-based GC soundness restated); the package's linker-specific results are T1, and no T3 novelty claim is made.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** When does section GC preserve program behaviour, and how does section granularity affect what is kept?

### R6b — `keptItem_of_keptItem_of_coarsening`

**Plain claim.** For item-level references E, root items R and item i: if the section assignment sec' factors through sec (sec' j = f (sec j) for every item j, for a map f that merges sections) and i is kept under sec, then i is kept under sec'.

**Kind / tier / depth.** theorem / T0 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Gc/Results.lean:316-318
theorem keptItem_of_keptItem_of_coarsening (E : List (Nat × Nat)) (R : Nat → Prop)
    (sec sec' f : Nat → Nat) (hc : ∀ i, sec' i = f (sec i)) (i : Nat)
    (h : KeptItem sec E R i) : KeptItem sec' E R i := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hc : ∀ i, sec' i = f (sec i)` | sec' is a coarsening of sec, with the merging map f exposed | tight: `coarsening_cex_refinement` (witness class: a three-item toy reference graph) |
| `h : KeptItem sec E R i` | the item is kept under the finer assignment | tight: `coarsening_cex_not_kept` (witness class: a three-item toy reference graph) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** secShared factors through secFine (f = secShared) and item 1 is kept under secFine (coarsening_nonvacuity). (`coarsening_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Items stand for functions, objects or bytes; the kept byte set grows because each item's bytes are kept with it. Section-level attributes such as KEEP are modeled as root items.
* Coarsening can strictly enlarge the kept set, and refining an assignment can shrink it: secShared factors through secFine (coarsening_nonvacuity), and unreferenced_item_kept_when_sharing_live_section proves that an unreferenced, non-root item 2 is removed with one item per section (secFine) and kept when it shares a section with the referenced item 1 (secShared). So "GC removes every unreferenced function" is false in the toy.
* Even with one item per section, GC keeps root items and every item referenced by a kept item, including references from code that never runs (E records static references, not executed ones).
* KeptItem models item-level references and root items; section-name-dependent rules (KEEP patterns, __start_X/__stop_X retention, COMDAT groups, SHF_GNU_RETAIN on merged sections) are not modeled.
* This is the transfer of reachability along a graph homomorphism, restated for section assignments; it is tiered T0.

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 2030-2039 (Texinfo markup removed): "--gc-sections decides which input sections are used by examining symbols and relocations. The section containing the entry symbol and all sections containing symbols undefined on the command-line will be kept, as will sections containing symbols referenced by dynamic objects. Note that when building shared libraries, the linker must assume that any visible symbol is referenced. Once this initial set of sections has been determined, the linker recursively marks as used any section referenced by their relocations. See --entry, --undefined, and --gc-keep-exported." Basis: documentation. Derived (modeling bridge): the toy's root flags and GcIn.Live (reachability from roots along relocation edges) have this shape.
* GCC 11.1.0 manual, Options That Control Optimization (gcc/doc/invoke.texi at tag releases/gcc-11.1.0, commit 50bc9185c2821350f0b785d6e23a6e9dcde58466, lines 12934-12937 and 12945-12947; HTML at https://gcc.gnu.org/onlinedocs/gcc-11.1.0/gcc/Optimize-Options.html): -ffunction-sections / -fdata-sections: "Place each function or data item into its own section in the output file if the target supports arbitrary sections. The name of the function or the name of the data item determines the section's name in the output file." and "Together with a linker garbage collection (linker --gc-sections option) these options may lead to smaller statically-linked executables (after stripping)." Basis: documentation. Derived (modeling bridge): finer section assignments are refinements in the sense of R6b.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** When does section GC preserve program behaviour, and how does section granularity affect what is kept?

### R7a — `precise_drops_unrooted_entries_of_noEdgeIntoName`

**Plain claim.** For every GC input g and name X: if no relocation edge reaches a section named X and no section named X is a root, then under the precise start/stop policy no section named X is kept; and if, in addition, a section kept under the precise policy references the bounds of X, the bounds are undefined (StartStopUndefined, the toy's link failure).

**Kind / tier / depth.** theorem / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Gc/Results.lean:369-372
theorem precise_drops_unrooted_entries_of_noEdgeIntoName (g : GcIn) (X : Nat)
    (hN : NoEdgeIntoName g X) (hU : ∀ j, g.nameOf j = some X → ¬ g.IsRoot j) :
    (∀ j, g.nameOf j = some X → ¬ g.Live .precise j) ∧
      ((∃ i, g.Live .precise i ∧ (i, X) ∈ g.ss) → StartStopUndefined g .precise X) := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hN : NoEdgeIntoName g X` | no relocation edge reaches a registry entry | tight: `precise_drops_cex_edge_into_entry` (witness class: a toy GC input of at most three sections) |
| `hU : ∀ j, g.nameOf j = some X → ¬ g.IsRoot j` | no entry is retained by a root class | tight: `precise_drops_cex_rooted_entry` (witness class: a toy GC input of at most three sections) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** gcReg [] false false (two entries named 7, bounds referenced by the entry section, no edges, no rooted entry) satisfies both hypotheses (registry_nonvacuity); registry_precise_link_failure_conservative_kept shows the link failure under the precise policy there. (`registry_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Modeling an undefined __start_X/__stop_X as a link failure is a toy choice; weak references and linker-script definitions of the bounds are not modeled.
* In the GNU ld and lld documentation quoted in the prior art, bounds synthesis and the conservative retention rule apply when the section name is representable as a C identifier, and a definition of __start_X or __stop_X in an object file or linker script prevents synthesis; neither condition is modeled.
* The second conjunct follows from the first: given that no entry is kept, a kept reference to the bounds is exactly StartStopUndefined. It records the toy's classification, not an additional fact about linkers.
* If no section is named X but a kept section references its bounds, RegistryKept holds vacuously and StartStopUndefined holds, under either policy (empty_registry_kept_and_undefined).
* With a relocation edge into one entry, the precise policy keeps that entry and removes the other while the bounds stay defined, so the registry shrinks without a link failure (registry_precise_silent_shrink); this is the witness behind the tightness of hN.
* The GC graph models relocation edges, four section-level root flags (entry, exported, KEEP, retain) and start/stop references. Static-archive member selection (which happens before section GC), COMDAT groups, SHF_LINK_ORDER dependencies, special-section roots such as init arrays and notes, dummy (R_*_NONE) relocations, /DISCARD/ rules, weak references, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 5506-5509 (Texinfo markup removed): "If an output section's name is the same as the input section's name and is representable as a C identifier, then the linker will automatically PROVIDE two symbols: __start_SECNAME and __stop_SECNAME, where SECNAME is the name of the section."; lines 5511-5512: "Note: most section names are not representable as C identifiers because they contain a . character."; lines 1595-1602 (item start-stop-gc): "When --gc-sections is in effect, a reference from a retained section to __start_SECNAME or __stop_SECNAME causes all input sections named SECNAME to also be retained, if SECNAME is representable as a C identifier and either __start_SECNAME or __stop_SECNAME is synthesized by the linker. -z start-stop-gc disables this effect, allowing sections to be garbage collected as if the special synthesized symbols were not defined."; lines 1602-1607: "-z start-stop-gc has no effect on a definition of __start_SECNAME or __stop_SECNAME in an object file or linker script. Such a definition will prevent the linker providing a synthesized __start_SECNAME or __stop_SECNAME respectively, and therefore the special treatment by garbage collection for those references."; ld/NEWS lines 142-143 (Changes in 2.37): "Add -z start-stop-gc to disable special treatment of __start_*/__stop_* references when --gc-sections." Basis: documentation. Derived (modeling bridge): the toy's conservative policy mirrors the retaining effect and the precise policy mirrors -z start-stop-gc; the C-identifier condition and user definitions of the bounds are not modeled.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ELF/start-stop-gc.rst lines 13-18: "__start_meta and __stop_meta are sometimes called encapsulation symbols. In October 2015, GNU ld switched behavior and made a __start_meta reference from a live section retain all meta input sections. This conservative behavior works for existing code which does not take GC into fair consideration, but unnecessarily increases sizes for modern metadata section usage which desires precise GC."; lines 21-22: "ld.lld 13.0.0 defaults to -z start-stop-gc and supports -z nostart-stop-gc to switch to the conservative behavior." (reStructuredText markup removed). Basis: documentation.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ld.lld.1 lines 929-933 (items start-stop-gc and nostart-stop-gc; mdoc markup removed): "Don't let __start_/__stop_ references retain the associated C identifier name sections (default)." and "Let __start_/__stop_ references retain the associated C identifier name sections." Basis: documentation.
* Background: F. Song (MaskRay), "Linker garbage collection", 2021-02-28, https://maskray.me/blog/2021-02-28-linker-garbage-collection (living document, snapshot 2026-11-21, line 416): "When -z nostart-stop-gc is in effect, if a live section contains a relocation referencing a symbol __start_$secname or __stop_$secname, and $secname has a C identifier name, all input sections $secname will be retained." Basis: documentation (practitioner write-up).

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Which retention mechanisms must a verified toolchain assume for data that the program reaches by iterating between __start_X and __stop_X, with no per-entry relocations?

### R7f — `registryKept_iff_of_noEdgeIntoName`

**Plain claim.** For every GC input g, policy pol and name X: if no relocation edge reaches a section named X, then GC keeps every section named X iff, for every section j named X, either j is a root, or the policy is conservative and some kept section references the bounds of X.

**Kind / tier / depth.** characterization / T1 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Gc/Results.lean:426-430
theorem registryKept_iff_of_noEdgeIntoName (g : GcIn) (pol : SSPolicy) (X : Nat)
    (hN : NoEdgeIntoName g X) :
    RegistryKept g pol X ↔
      ∀ j, g.nameOf j = some X →
        g.IsRoot j ∨ (pol = .conservative ∧ ∃ i, g.Live pol i ∧ (i, X) ∈ g.ss) := by
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `hN : NoEdgeIntoName g X` | no relocation edge reaches a registry entry | tight: `registryKept_iff_cex_edges_into_entries` (witness class: a toy GC input of at most three sections) |

Each `tight` entry names a theorem stating that a concrete instance of the recorded class satisfies all the other hypotheses while the conclusion fails; `harmless` marks a hypothesis whose removal keeps the statement true.

**Non-vacuity.** gcReg [] false false with X = 7 satisfies hN (registry_nonvacuity); both sides are false under the precise policy and true under the conservative policy (registry_precise_link_failure_conservative_kept). (`registry_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Behaviour preservation for a program that iterates a registry is connected to runs by the bridge lemma runPreserved_registryScan_iff_registryKept: the run registryScan g i X, in which section i iterates the bounds of X and reaches every section named X, is preserved by GC iff RegistryKept g pol X.
* The pointwise form is the auxiliary lemma live_iff_root_or_conservative_reference_of_noEdgeIntoName (hypotheses hN and hj : g.nameOf j = some X, the latter tight by registry_iff_cex_other_name). Its two directions specialize to the auxiliary lemmas conservative_registryKept_of_live_reference (under the conservative policy a kept reference keeps every entry; hypotheses tight by conservative_cex_dead_referencer and conservative_cex_no_reference; instance conservative_registryKept_nonvacuity) and registryKept_of_entries_rooted (rooted entries are kept under either policy; hypothesis tight by rooted_cex_unrooted; instance registryKept_of_entries_rooted_nonvacuity).
* The hypothesis NoEdgeIntoName is tight over three-section toy inputs: without it, entries reached by relocation edges are kept under the precise policy although no entry is rooted (registryKept_iff_cex_edges_into_entries, registry_precise_silent_shrink).
* In the GNU ld and lld documentation quoted in the prior art, bounds synthesis and the conservative retention rule apply when the section name is representable as a C identifier, and a definition of __start_X or __stop_X in an object file or linker script prevents synthesis; neither condition is modeled.
* Marking entries as roots (KEEP or the retain flag) in the toy does not model static-archive member selection, COMDAT resolution, /DISCARD/ rules, compiler-stage elimination (R8b), or linkers and OSABIs that ignore SHF_GNU_RETAIN.

**Prior art.**

* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 5506-5509 (Texinfo markup removed): "If an output section's name is the same as the input section's name and is representable as a C identifier, then the linker will automatically PROVIDE two symbols: __start_SECNAME and __stop_SECNAME, where SECNAME is the name of the section."; lines 5511-5512: "Note: most section names are not representable as C identifiers because they contain a . character."; lines 1595-1602 (item start-stop-gc): "When --gc-sections is in effect, a reference from a retained section to __start_SECNAME or __stop_SECNAME causes all input sections named SECNAME to also be retained, if SECNAME is representable as a C identifier and either __start_SECNAME or __stop_SECNAME is synthesized by the linker. -z start-stop-gc disables this effect, allowing sections to be garbage collected as if the special synthesized symbols were not defined."; lines 1602-1607: "-z start-stop-gc has no effect on a definition of __start_SECNAME or __stop_SECNAME in an object file or linker script. Such a definition will prevent the linker providing a synthesized __start_SECNAME or __stop_SECNAME respectively, and therefore the special treatment by garbage collection for those references."; ld/NEWS lines 142-143 (Changes in 2.37): "Add -z start-stop-gc to disable special treatment of __start_*/__stop_* references when --gc-sections." Basis: documentation. Derived (modeling bridge): the toy's conservative policy mirrors the retaining effect and the precise policy mirrors -z start-stop-gc; the C-identifier condition and user definitions of the bounds are not modeled.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ELF/start-stop-gc.rst lines 13-18: "__start_meta and __stop_meta are sometimes called encapsulation symbols. In October 2015, GNU ld switched behavior and made a __start_meta reference from a live section retain all meta input sections. This conservative behavior works for existing code which does not take GC into fair consideration, but unnecessarily increases sizes for modern metadata section usage which desires precise GC."; lines 21-22: "ld.lld 13.0.0 defaults to -z start-stop-gc and supports -z nostart-stop-gc to switch to the conservative behavior." (reStructuredText markup removed). Basis: documentation.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ld.lld.1 lines 929-933 (items start-stop-gc and nostart-stop-gc; mdoc markup removed): "Don't let __start_/__stop_ references retain the associated C identifier name sections (default)." and "Let __start_/__stop_ references retain the associated C identifier name sections." Basis: documentation.
* GNU ld manual, binutils 2.42, ld/ld.texi lines 5462-5466 (node Input Section Keep): "When link-time garbage collection is in use (--gc-sections), it is often useful to mark sections that should not be eliminated. This is accomplished by surrounding an input section's wildcard entry with KEEP(), as in KEEP(*(.init)) or KEEP(SORT_BY_NAME(*)(.ctors))." Basis: documentation.
* GNU ld manual, binutils 2.42 (tag binutils-2_42, commit c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9), ld/ld.texi lines 2047-2048: "As a GNU extension, ELF input sections marked with the SHF_GNU_RETAIN flag will not be garbage collected." Basis: documentation.
* binutils 2.36 (tag binutils-2_36, commit 9288e0fae61b716ce75334be906283de8b18b787), ld/NEWS lines 44-46: "Add support for the SHF_GNU_RETAIN ELF section flag. This flag specifies that the section should not be garbage collected by the linker."; gas/NEWS lines 54-57: "Add support for the SHF_GNU_RETAIN flag, which can be applied to sections using the 'R' flag in the .section directive. SHF_GNU_RETAIN specifies that the section should not be garbage collected by the linker. It requires the GNU or FreeBSD ELF OSABIs." Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** Which retention mechanisms must a verified toolchain assume for data that the program reaches by iterating between __start_X and __stop_X, with no per-entry relocations?

### R8a — `survives_iff_compiledPath`

**Plain claim.** For every program p (statics, each emitted into its own input section, and source-level link edges p.ledges) and static i: i survives end-to-end (the compiler stage emits it and linker GC keeps its section in the object the compiler produced) iff there is a path in p.ledges from a static whose section is a link root or retained to i, every static of which, the start and i included, the compiler stage keeps (it is referenced by compiler-kept code or compiler-used).

**Kind / tier / depth.** characterization / T0 / shallow.

**Basis.** execution (Lean kernel check): the Lean statement below and every witness and counterexample named in this card.

**Lean statement.**

```lean
-- lean/ToyRelroGc/Gc/Results.lean:568-569
theorem survives_iff_compiledPath (p : Prog2) (i : Nat) :
    p.Survives i ↔ p.CompiledPath i := by
```

**Hypothesis ledger.**

No side-condition hypotheses (the statement is universally quantified over its arguments).

**Non-vacuity.** No side-condition hypotheses (universally quantified over p and i). twoStage_nonvacuity: in Prog2.mk [stMain, stUsedRetained] [], static 1 (compiler-used and retained) survives and has a compiler-kept path; compiledPath_examples gives a static with no such path. (`twoStage_nonvacuity`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* survives_iff_linkReach: survival coincides with link-time reachability in the object the compiler produced, because that object's roots and edges lie on compiler-kept statics (compiled_of_linkReach). The conjunction form survives_iff_compileKept_and_linkReach_or_retain ((referenced at compile time or compiler-used) and (link-reachable or retained), for the record s with p.statics[i]? = some s) is therefore a definitional restatement: link reachability implies both its left conjunct and its right disjunction. Without the lookup binding the conjunction form is false (survives_conjunction_cex_without_lookup).
* Source-level reachability plus compiler retention does not imply survival (compileKept_and_srcReach_not_sufficient, card R8b): paths through statics the compiler drops do not count.
* The toy's compiler stage keeps a static iff it is referenced by compiler-kept code or compiler-used; compiler optimizations that remove referenced statics, LTO, and section merging are not modeled.
* Attribute designs differ across toolchains and layers, and the toy fixes none of them: its flags cref, cused, retain and lroot are independent. LLVM IR @llvm.used binds the compiler, assembler and linker (LangRef); C/C++ __attribute__((retain)) in GCC 11 and Clang is a separate attribute from used, and the Clang documentation states that it has no effect if the compiler does not emit the definition and that it is typically combined with used; whether unstable Rust #[used(linker)] implies #[used(compiler)] is listed as an unresolved question in rust-lang/rust issue 93798 (an open tracking issue, cited as background, not as normative).
* Prog2 places each static in its own input section (as with -fdata-sections). Without per-static sections a static can survive linker GC by sharing a kept section; the item-level model of R6b exhibits this (unreferenced_item_kept_when_sharing_live_section).
* Surviving both stages in Prog2 does not establish presence in a real final binary: static-archive member selection, COMDAT deduplication, /DISCARD/ rules, LTO, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.
* This is reachability in the subgraph induced by the compiler-kept statics, restated; it is tiered T0.

**Prior art.**

* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), clang/include/clang/Basic/AttrDocs.td, RetainDocs lines 97-99: "This attribute, when attached to a function or variable definition, prevents section garbage collection in the linker. It does not prevent other discard mechanisms, such as archive member selection, and COMDAT group resolution."; lines 101-105: "If the compiler does not emit the definition, e.g. because it was not used in the translation unit or the compiler was able to eliminate all of the uses, this attribute has no effect. This attribute is typically combined with the used attribute to force the definition to be emitted and preserved into the final linked image."; UsedDocs lines 86-88: "On ELF targets, it has no effect on its own, and the linker may remove the definition if it is not otherwise referenced. This linker GC can be avoided by also adding the retain attribute." (reStructuredText markup removed). Basis: documentation. Derived (modeling bridge): `retain` without `used` on a static that the compiler does not otherwise keep corresponds to the toy record stRetainOnly (retain = true, cref = cused = false), the configuration of retained_but_compiler_dropped.
* GCC 11.1.0 manual, Common Variable Attributes (gcc/doc/extend.texi at tag releases/gcc-11.1.0, commit 50bc9185c2821350f0b785d6e23a6e9dcde58466, lines 7514-7516 and 7524-7530; HTML at https://gcc.gnu.org/onlinedocs/gcc-11.1.0/gcc/Common-Variable-Attributes.html): used: "This attribute, attached to a variable with static storage, means that the variable must be emitted even if it appears that the variable is not referenced."; retain: "For ELF targets that support the GNU or FreeBSD OSABIs, this attribute will save the variable from linker garbage collection. To support this behavior, variables that have not been placed in specific sections (e.g. by the section attribute, or the -fdata-sections option), will be placed in new, unique sections." and "This additional functionality requires Binutils version 2.36 or later." Basis: documentation. The two entries are separate attributes; neither entry says that one implies the other.
* LLVM 19.1.0 (commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), llvm/docs/LangRef.rst lines 8715-8719: "If a symbol appears in the @llvm.used list, then the compiler, assembler, and linker are required to treat the symbol as if there is a reference to the symbol that it cannot see (which is why they have to be named). For example, if a variable has internal linkage and no references other than that from the @llvm.used list, it cannot be deleted."; lines 8732-8734: "The @llvm.compiler.used directive is the same as the @llvm.used directive, except that it only prevents the compiler from touching the symbol." Basis: normative (IR specification).
* The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/abi.md line 14: "The used attribute forces a static to be kept in the output object file (.o, .rlib, etc., excluding final binaries) even if it's never used or referenced by any other item in the crate. The linker, however, is still free to remove it." Basis: documentation.
* rust-lang/rust issue 93798, "Tracking Issue for used_with_arg" (open tracking issue, living document; cited as background and not relied on as normative; body snapshot 2026-11-21, lines 5-6): "The #[used(compiler)] attribute indicates that the symbol should be considered used at the compiler level. It should not be eliminated by the compiler even if it appears unreferenced. This attribute guarantees that the symbol will make it to the linker." and "The #[used(linker)] attribute indicates that the symbol should additionally be considered used at the linker level. The linker should not eliminate the symbol even if it appears unreferenced."; its Unresolved Questions list (line 28) includes: "Does #[used(linker)] imply #[used(compiler)] or does it mean the symbol is only considered used if it actually makes it past the compiler?" (Markdown markup removed). Basis: documentation of an unstable feature.
* binutils 2.36 (tag binutils-2_36, commit 9288e0fae61b716ce75334be906283de8b18b787), ld/NEWS lines 44-46: "Add support for the SHF_GNU_RETAIN ELF section flag. This flag specifies that the section should not be garbage collected by the linker."; gas/NEWS lines 54-57: "Add support for the SHF_GNU_RETAIN flag, which can be applied to sections using the 'R' flag in the .section directive. SHF_GNU_RETAIN specifies that the section should not be garbage collected by the linker. It requires the GNU or FreeBSD ELF OSABIs." Basis: documentation.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ELF/start-stop-gc.rst lines 51-53: "On ELF targets, __attribute__((used)) prevents compiler discarding, but does not affect linker --gc-sections."; lines 39-40 and 46: "If a relocation is inconvenient, consider using __attribute__((retain)) (GCC 11 with modern binutils, Clang 13)." followed by the example `__attribute__((retain,used,section("meta")))` (reStructuredText markup removed). Basis: documentation.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** What must hold at each of the compiler and linker stages for a static to be present in the final binary?

### R8b — `compilerUsed_unretained_unreachable_removed`, `retained_but_compiler_dropped`, `compileKept_and_srcReach_not_sufficient`

**Plain claim.** (i) In Prog2.mk [stMain, stUsedOnly] [], the compiler-used static 1, in its own section and neither retained nor reachable at link time, survives the compiler stage and is removed by linker GC. (ii) In Prog2.mk [stMain, stRetainOnly] [], static 1, whose section carries the retain flag but which is neither referenced at compile time nor compiler-used, is dropped by the compiler stage and does not survive. (iii) In Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)], static 2 is compiler-used and reachable from the entry static 0 in the source-level link graph, but its sole path passes through static 1, which no flag keeps and the compiler stage drops; static 2 does not survive.

**Kind / tier / depth.** counterexample / T1 / definitional.

**Basis.** execution (Lean kernel check): the Lean statements below and every witness and counterexample named in this card.

**Lean statements.**

```lean
-- lean/ToyRelroGc/Gc/Results.lean:643-645
theorem compilerUsed_unretained_unreachable_removed :
    (Prog2.mk [stMain, stUsedOnly] []).compiled 1 = true ∧
      ¬ (Prog2.mk [stMain, stUsedOnly] []).Survives 1 := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:654-656
theorem retained_but_compiler_dropped :
    stRetainOnly.retain = true ∧ (Prog2.mk [stMain, stRetainOnly] []).compiled 1 = false ∧
      ¬ (Prog2.mk [stMain, stRetainOnly] []).Survives 1 := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:672-675
theorem compileKept_and_srcReach_not_sufficient :
    (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).compiled 2 = true ∧
      (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).SrcReach 2 ∧
      ¬ (Prog2.mk [stMain, stPlain, stUsedOnly] [(0, 1), (1, 2)]).Survives 2 := by
```

**Hypothesis ledger.**

Concrete instances; no hypotheses.

**Non-vacuity.** Concrete programs with two or three statics; each fact is proved for the stated program. (`compilerUsed_unretained_unreachable_removed`)

**Non-claims.**

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Instance (i) is the toy counterpart of the documented gap between compiler-level and linker-level retention (the GCC and Clang used entries, lld's start-stop-gc document, LangRef's @llvm.compiler.used, the Rust Reference's used attribute).
* Instance (ii) is the configuration that the Clang documentation describes for __attribute__((retain)) on a definition the compiler does not emit ("this attribute has no effect"); this is why the Clang and lld documentation combine retain with used. Attribute designs differ across toolchains and layers, and the toy fixes none of them: its flags cref, cused, retain and lroot are independent. LLVM IR @llvm.used binds the compiler, assembler and linker (LangRef); C/C++ __attribute__((retain)) in GCC 11 and Clang is a separate attribute from used, and the Clang documentation states that it has no effect if the compiler does not emit the definition and that it is typically combined with used; whether unstable Rust #[used(linker)] implies #[used(compiler)] is listed as an unresolved question in rust-lang/rust issue 93798 (an open tracking issue, cited as background, not as normative).
* Instance (iii) uses realistic flag combinations (an entry, a plain static, a compiler-used static); it shows that the second stage is reachability over compiler-kept statics (R8a), not source-level reachability.
* Prog2 places each static in its own input section (as with -fdata-sections). Without per-static sections a static can survive linker GC by sharing a kept section; the item-level model of R6b exhibits this (unreferenced_item_kept_when_sharing_live_section).
* Surviving both stages in Prog2 does not establish presence in a real final binary: static-archive member selection, COMDAT deduplication, /DISCARD/ rules, LTO, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.
* These are single concrete toy instances; they show the corresponding informal claims are false as stated in the toy, not how often real programs are affected.

**Prior art.**

* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), clang/include/clang/Basic/AttrDocs.td, RetainDocs lines 97-99: "This attribute, when attached to a function or variable definition, prevents section garbage collection in the linker. It does not prevent other discard mechanisms, such as archive member selection, and COMDAT group resolution."; lines 101-105: "If the compiler does not emit the definition, e.g. because it was not used in the translation unit or the compiler was able to eliminate all of the uses, this attribute has no effect. This attribute is typically combined with the used attribute to force the definition to be emitted and preserved into the final linked image."; UsedDocs lines 86-88: "On ELF targets, it has no effect on its own, and the linker may remove the definition if it is not otherwise referenced. This linker GC can be avoided by also adding the retain attribute." (reStructuredText markup removed). Basis: documentation. Derived (modeling bridge): `retain` without `used` on a static that the compiler does not otherwise keep corresponds to the toy record stRetainOnly (retain = true, cref = cused = false), the configuration of retained_but_compiler_dropped.
* GCC 11.1.0 manual, Common Variable Attributes (gcc/doc/extend.texi at tag releases/gcc-11.1.0, commit 50bc9185c2821350f0b785d6e23a6e9dcde58466, lines 7514-7516 and 7524-7530; HTML at https://gcc.gnu.org/onlinedocs/gcc-11.1.0/gcc/Common-Variable-Attributes.html): used: "This attribute, attached to a variable with static storage, means that the variable must be emitted even if it appears that the variable is not referenced."; retain: "For ELF targets that support the GNU or FreeBSD OSABIs, this attribute will save the variable from linker garbage collection. To support this behavior, variables that have not been placed in specific sections (e.g. by the section attribute, or the -fdata-sections option), will be placed in new, unique sections." and "This additional functionality requires Binutils version 2.36 or later." Basis: documentation. The two entries are separate attributes; neither entry says that one implies the other.
* LLVM 19.1.0 (tag llvmorg-19.1.0, commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), lld/docs/ELF/start-stop-gc.rst lines 51-53: "On ELF targets, __attribute__((used)) prevents compiler discarding, but does not affect linker --gc-sections."; lines 39-40 and 46: "If a relocation is inconvenient, consider using __attribute__((retain)) (GCC 11 with modern binutils, Clang 13)." followed by the example `__attribute__((retain,used,section("meta")))` (reStructuredText markup removed). Basis: documentation.
* LLVM 19.1.0 (commit a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4), llvm/docs/LangRef.rst lines 8715-8719: "If a symbol appears in the @llvm.used list, then the compiler, assembler, and linker are required to treat the symbol as if there is a reference to the symbol that it cannot see (which is why they have to be named). For example, if a variable has internal linkage and no references other than that from the @llvm.used list, it cannot be deleted."; lines 8732-8734: "The @llvm.compiler.used directive is the same as the @llvm.used directive, except that it only prevents the compiler from touching the symbol." Basis: normative (IR specification).
* The Rust Reference (rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c), src/abi.md line 14: "The used attribute forces a static to be kept in the output object file (.o, .rlib, etc., excluding final binaries) even if it's never used or referenced by any other item in the crate. The linker, however, is still free to remove it." Basis: documentation.
* rust-lang/rust issue 93798, "Tracking Issue for used_with_arg" (open tracking issue, living document; cited as background and not relied on as normative; body snapshot 2026-11-21, lines 5-6): "The #[used(compiler)] attribute indicates that the symbol should be considered used at the compiler level. It should not be eliminated by the compiler even if it appears unreferenced. This attribute guarantees that the symbol will make it to the linker." and "The #[used(linker)] attribute indicates that the symbol should additionally be considered used at the linker level. The linker should not eliminate the symbol even if it appears unreferenced."; its Unresolved Questions list (line 28) includes: "Does #[used(linker)] imply #[used(compiler)] or does it mean the symbol is only considered used if it actually makes it past the compiler?" (Markdown markup removed). Basis: documentation of an unstable feature.

**Basis (real systems).** derived (modeling bridge): each prior-art entry above marked "Derived (modeling bridge)" states which toy definition it corresponds to and why; that correspondence rests on the quoted documentation or source at the pinned revision, not on the Lean proof. Entries labelled `documentation`, `normative` or `source` alone are cited for context and make no further claim about the toy.

**Design question.** What must hold at each of the compiler and linker stages for a static to be present in the final binary?

### Auxiliary lemmas and definitions cited by name (verbatim)

Every package-local name that this report mentions is quoted verbatim in this section or in the sections above, and is recorded with its hashes under Evidence.

```lean
-- lean/ToyRelroGc/Relro/Basic.lean:86-90
theorem trace_twoPhase (c : Cfg) (sa : SymTab) (ops : List Op) :
    trace c sa (twoPhase c ops) =
      { applyOuts := c.relocs.map (fun r => if mapWr c.kinds r.slot then Out.ok else Out.fault)
        opOuts := (runT c sa (postLoad c sa) (ops.map Ev.op)).opOuts
        memAtProtect := some (tryApplyAll sa (mapWr c.kinds) c.relocs c.init) } := by
```

```lean
-- lean/ToyRelroGc/Relro/Basic.lean:143-144
theorem loadOk_twoPhase_iff (c : Cfg) (sa : SymTab) (ops : List Op) :
    LoadOk (trace c sa (twoPhase c ops)) ↔ RelocSlotsWritable c := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:201-206
theorem linkResolved_rodata_loadOk_writeFaultsAfter_and_image (c : Cfg) (saL saR : SymTab)
    (s : Nat) (hk : c.kinds[s]? = some .ro) :
    LoadOk (trace (linkResolve saL c) saR (twoPhase (linkResolve saL c) [])) ∧
      WriteFaultsAfter (linkResolve saL c) saR s ∧
      (trace (linkResolve saL c) saR (twoPhase (linkResolve saL c) [])).memAtProtect =
        some (applyAll saL c.relocs c.init) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:559-562
theorem pic_rodata_cex_link_resolved :
    ¬ symReloc 0 0 ∈ (linkResolve sa0 cfgSlotRo).relocs ∧
      (linkResolve sa0 cfgSlotRo).kinds[(symReloc 0 0).slot]? = some .ro ∧
      LoadOk (trace (linkResolve sa0 cfgSlotRo) sa0 (twoPhase (linkResolve sa0 cfgSlotRo) [])) := by
```

```lean
-- lean/ToyRelroGc/Relro/Basic.lean:157-158
theorem writeFaultsAfter_iff (c : Cfg) (sa : SymTab) (a : Nat) :
    WriteFaultsAfter c sa a ↔ (mapWr c.kinds a && !c.prot a) = false := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:133-138
theorem pic_data_slot_loads_and_write_succeeds (c : Cfg) (sa : SymTab) (r : Reloc)
    (hr : r ∈ c.relocs) (hWr : RelocSlotsWritable c) (hk : c.kinds[r.slot]? = some .mutable)
    (hAvoid : ProtAvoidsMut c) :
    LoadOk (trace c sa (twoPhase c [])) ∧
      ∀ (ops : List Op) (v : Nat),
        (trace c sa (twoPhase c (ops ++ [.write r.slot v]))).opOuts[ops.length]? = some .ok := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:154-157
theorem pic_relro_slot_loads_and_writeFaultsAfter (c : Cfg) (sa : SymTab) (r : Reloc)
    (hr : r ∈ c.relocs) (hWr : RelocSlotsWritable c) (hk : c.kinds[r.slot]? = some .relro)
    (hCover : ProtCoversRelro c) :
    LoadOk (trace c sa (twoPhase c [])) ∧ WriteFaultsAfter c sa r.slot := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:339-342
theorem data_slot_cex_load_fault :
    symReloc 1 0 ∈ cfgRoMutReloc.relocs ∧ ¬ RelocSlotsWritable cfgRoMutReloc ∧
      cfgRoMutReloc.kinds[(symReloc 1 0).slot]? = some .mutable ∧ ProtAvoidsMut cfgRoMutReloc ∧
      ¬ LoadOk (trace cfgRoMutReloc sa0 (twoPhase cfgRoMutReloc [])) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:347-351
theorem data_slot_cex_relro_slot :
    symReloc 0 0 ∈ goodCfg.relocs ∧ RelocSlotsWritable goodCfg ∧
      goodCfg.kinds[(symReloc 0 0).slot]? ≠ some .mutable ∧ ProtAvoidsMut goodCfg ∧
      (trace goodCfg sa0 (twoPhase goodCfg ([] ++ [.write (symReloc 0 0).slot 9]))).opOuts[
        ([] : List Op).length]? ≠ some .ok := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:356-360
theorem data_slot_cex_covered :
    symReloc 0 0 ∈ cfgMutCovered.relocs ∧ RelocSlotsWritable cfgMutCovered ∧
      cfgMutCovered.kinds[(symReloc 0 0).slot]? = some .mutable ∧ ¬ ProtAvoidsMut cfgMutCovered ∧
      (trace cfgMutCovered sa0 (twoPhase cfgMutCovered ([] ++ [.write (symReloc 0 0).slot 9]))).opOuts[
        ([] : List Op).length]? ≠ some .ok := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:367-370
theorem relro_slot_cex_load_fault :
    symReloc 0 0 ∈ cfgRelroRo.relocs ∧ ¬ RelocSlotsWritable cfgRelroRo ∧
      cfgRelroRo.kinds[(symReloc 0 0).slot]? = some .relro ∧ ProtCoversRelro cfgRelroRo ∧
      ¬ LoadOk (trace cfgRelroRo sa0 (twoPhase cfgRelroRo [])) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:375-378
theorem relro_slot_cex_mut_slot :
    symReloc 0 0 ∈ cfgMutReloc.relocs ∧ RelocSlotsWritable cfgMutReloc ∧
      cfgMutReloc.kinds[(symReloc 0 0).slot]? ≠ some .relro ∧ ProtCoversRelro cfgMutReloc ∧
      ¬ WriteFaultsAfter cfgMutReloc sa0 (symReloc 0 0).slot := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:383-386
theorem relro_slot_cex_no_cover :
    symReloc 0 0 ∈ cfgNoProt.relocs ∧ RelocSlotsWritable cfgNoProt ∧
      cfgNoProt.kinds[(symReloc 0 0).slot]? = some .relro ∧ ¬ ProtCoversRelro cfgNoProt ∧
      ¬ WriteFaultsAfter cfgNoProt sa0 (symReloc 0 0).slot := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:49-51
theorem lazy_inside_protect_writeFaultsAfter_first_call_faults :
    LazyBound lazyRelroCfg 0 0 ∧ WriteFaultsAfter lazyRelroCfg sa0 0 ∧
      (trace lazyRelroCfg sa0 (twoPhase lazyRelroCfg [.call 0])).opOuts = [.fault] := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:58-61
theorem partial_relro_lazy_slot_write_redirects_call :
    LazyBound lazyMutCfg 0 0 ∧ CallWorks lazyMutCfg sa0 0 0 ∧
      (trace lazyMutCfg sa0 (twoPhase lazyMutCfg [.write 0 55, .call 0])).opOuts =
        [.ok, .jump 55] ∧ sa0 0 ≠ 55 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:40-42
theorem eager_relro_callWorks_and_writeFaultsAfter :
    ¬ LazyBound eagerCfg 0 0 ∧ EagerBound eagerCfg 0 0 ∧ CallWorks eagerCfg sa0 0 0 ∧
      WriteFaultsAfter eagerCfg sa0 0 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:75-76
theorem eagerRelroOrLazy_of_eagerRelroOrLazyMut (c : Cfg) (B : List (Nat × Sym))
    (h : EagerRelroOrLazyMut c B) : EagerRelroOrLazy c B := by
```

```lean
-- lean/ToyRelroGc/Relro/Basic.lean:117-119
theorem tryApplyAll_bind (sa : SymTab) (w : Nat → Bool) (x : Nat) (t : Sym) (hw : w x = true) :
    ∀ (rs : List Reloc) (m : Mem), (∀ r ∈ rs, r.slot = x → r = bindReloc x t) →
      (m x = sa t ∨ bindReloc x t ∈ rs) → tryApplyAll sa w rs m x = sa t
```

```lean
-- lean/ToyRelroGc/Relro/Basic.lean:105-106
theorem tryApplyAll_other (sa : SymTab) (w : Nat → Bool) (x : Nat) :
    ∀ (rs : List Reloc) (m : Mem), (∀ r ∈ rs, r.slot ≠ x) → tryApplyAll sa w rs m x = m x
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:358-360
theorem downDown_avoidsMut_cex_firstPage :
    RelroIs layoutMutRelro 1 2 ∧ ¬ NoMutIn layoutMutRelro (alignDown 2 1) 1 ∧
      ¬ AvoidsMut layoutMutRelro (roundedMask .downDown 2 1 2) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:340-347
theorem endAligned_firstPage_mut_no_pageGranular_protection :
    RelroIs layoutMutRelro 1 2 ∧ 2 % 2 = 0 ∧ NoMutIn layoutMutRelro 2 (alignUp 2 2) ∧
      ¬ (∃ m, PageGranular 2 m ∧ CoversRelro layoutMutRelro m ∧ AvoidsMut layoutMutRelro m) ∧
      CoversRelro layoutMutRelro (roundedMask .downDown 2 1 2) ∧
      ¬ AvoidsMut layoutMutRelro (roundedMask .downDown 2 1 2) ∧
      (trace (protCfg layoutMutRelro (roundedMask .downDown 2 1 2)) sa0
        (twoPhase (protCfg layoutMutRelro (roundedMask .downDown 2 1 2)) [.write 0 9])).opOuts =
        [.fault] := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:418-424
theorem pageRounding_nonvacuity :
    0 < 2 ∧ RelroIs [.relro, .relro, .mutable] 0 2 ∧ 0 < 2 ∧
      NoMutIn [.relro, .relro, .mutable] (alignDown 2 0) 0 ∧
      CoversRelro [.relro, .relro, .mutable] (roundedMask .downDown 2 0 2) ∧
      AvoidsMut [.relro, .relro, .mutable] (roundedMask .downDown 2 0 2) ∧
      CoversRelro [.relro, .relro, .mutable] (roundedMask .downUp 2 0 2) ∧
      AvoidsMut [.relro, .relro, .mutable] (roundedMask .downUp 2 0 2) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:316-321
theorem downDown_unpaddedEnd_tail_write_succeeds :
    RelroIs layoutRelro3 0 3 ∧ 3 % 2 ≠ 0 ∧
      ¬ CoversRelro layoutRelro3 (roundedMask .downDown 2 0 3) ∧
      (trace (protCfg layoutRelro3 (roundedMask .downDown 2 0 3)) sa0
        (twoPhase (protCfg layoutRelro3 (roundedMask .downDown 2 0 3)) [.write 2 9])).opOuts =
        [.ok] := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:13
theorem le_alignUp (P a : Nat) (hP : 0 < P) : a ≤ alignUp P a := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:229-230
theorem roundedMask_eq_false_of_le (pol : Rounding) (P rs re : Nat) (h : re ≤ rs) (a : Nat) :
    roundedMask pol P rs re a = false := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:327-332
theorem downUp_sharedLastPage_mut_write_faults :
    RelroIs layoutRelro3Mut 0 3 ∧ CoversRelro layoutRelro3Mut (roundedMask .downUp 2 0 3) ∧
      ¬ AvoidsMut layoutRelro3Mut (roundedMask .downUp 2 0 3) ∧
      (trace (protCfg layoutRelro3Mut (roundedMask .downUp 2 0 3)) sa0
        (twoPhase (protCfg layoutRelro3Mut (roundedMask .downUp 2 0 3)) [.write 3 9])).opOuts =
        [.fault] := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:277-280
theorem downUp_covers_avoids_iff_exists_pageGranular (P rs re : Nat) (L : List Kind)
    (hP : 0 < P) (hR : RelroIs L rs re) (hne : rs < re) :
    (CoversRelro L (roundedMask .downUp P rs re) ∧ AvoidsMut L (roundedMask .downUp P rs re)) ↔
      ∃ m, PageGranular P m ∧ CoversRelro L m ∧ AvoidsMut L m := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:258-259
theorem roundedMask_downUp_pageGranular (P rs re : Nat) :
    PageGranular P (roundedMask .downUp P rs re) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:288-291
theorem noncontiguous_relro_noSharedPage_no_single_interval :
    NoSharedPage 1 [.relro, .mutable, .relro] ∧
      ¬ ∃ lo hi : Nat, CoversRelro [.relro, .mutable, .relro] (rangeMask lo hi) ∧
        AvoidsMut [.relro, .mutable, .relro] (rangeMask lo hi) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:21-22
theorem alignUp_eq_self_of_mod_eq_zero (P a : Nat) (hP : 0 < P) (h : a % P = 0) :
    alignUp P a = a := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:193-195
theorem noSharedPage_iff_partialPages_noMut (P rs re : Nat) (L : List Kind) (hP : 0 < P)
    (hR : RelroIs L rs re) (hne : rs < re) :
    NoSharedPage P L ↔ NoMutIn L (alignDown P rs) rs ∧ NoMutIn L re (alignUp P re) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:408-412
theorem noSharedPage_iff_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs [.relro, .mutable] 0 1 ∧ (0 : Nat) < 1 ∧
      ¬ (NoSharedPage 0 [.relro, .mutable] ↔
        NoMutIn [.relro, .mutable] (alignDown 0 0) 0 ∧
          NoMutIn [.relro, .mutable] 1 (alignUp 0 1)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:616-619
theorem noSharedPage_iff_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs layoutRelro3Mut 0 2 ∧ 0 < 2 ∧
      ¬ (NoSharedPage 2 layoutRelro3Mut ↔
        NoMutIn layoutRelro3Mut (alignDown 2 0) 0 ∧ NoMutIn layoutRelro3Mut 2 (alignUp 2 2)) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:401-404
theorem noSharedPage_iff_cex_empty :
    (0 : Nat) < 2 ∧ RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ (NoSharedPage 2 [.mutable] ↔
        NoMutIn [.mutable] (alignDown 2 1) 1 ∧ NoMutIn [.mutable] 1 (alignUp 2 1)) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:430-433
theorem applyReloc_comm (sa : SymTab) (S : Nat → Prop) (x y : Reloc)
    (hx : x.ReadsOnly S) (hy : y.ReadsOnly S) (hxs : ¬ S x.slot) (hys : ¬ S y.slot)
    (hne : x.slot ≠ y.slot) (m : Mem) :
    applyReloc sa (applyReloc sa m x) y = applyReloc sa (applyReloc sa m y) x := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:451-454
theorem applyAll_perm_of_readsOnly_of_slots_outside (sa : SymTab) (S : Nat → Prop)
    {rs rs' : List Reloc} (p : rs.Perm rs') :
    (∀ r ∈ rs, r.ReadsOnly S) → (∀ r ∈ rs, ¬ S r.slot) → (rs.map Reloc.slot).Nodup →
      ∀ m, applyAll sa rs m = applyAll sa rs' m := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:650-653
theorem addressOnlyOrder_nonvacuity :
    [rAddr0, symReloc 2 1].Perm [symReloc 2 1, rAddr0] ∧
      (∀ r ∈ [rAddr0, symReloc 2 1], r.AddressOnly) ∧
      ([rAddr0, symReloc 2 1].map Reloc.slot).Nodup := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:515-520
theorem resolver_reads_unrelocated_slot_order_dependent :
    [rAddr0, rRes1].Perm [rRes1, rAddr0] ∧ ([rAddr0, rRes1].map Reloc.slot).Nodup ∧
      ¬ (∀ r ∈ [rAddr0, rRes1], r.AddressOnly) ∧
      applyAll sa0 [rAddr0, rRes1] (fun _ => 0) ≠ applyAll sa0 [rRes1, rAddr0] (fun _ => 0) ∧
      applyAll sa0 [rAddr0, rRes1] (fun _ => 0) 1 = 100 ∧
      applyAll sa0 [rRes1, rAddr0] (fun _ => 0) 1 = 0 := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:662-669
theorem relocationOrder_nonvacuity :
    (∀ r ∈ [rAddr0, symReloc 2 1], r.AddressOnly) ∧
      ([rAddr0, symReloc 2 1].map Reloc.slot).Nodup ∧
      (∀ r ∈ [rRes1, rRes3of2, rRes4of9],
        r.ReadsOnly (fun a => a ∉ [rRes1, rRes3of2, rRes4of9].map Reloc.slot)) ∧
      ([rRes1, rRes3of2, rRes4of9].map Reloc.slot).Nodup ∧
      [symReloc 2 1, rAddr0].Perm [rAddr0, symReloc 2 1] ∧
      [rRes4of9, rRes3of2, rRes1].Perm [rRes1, rRes3of2, rRes4of9] := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:55-58
theorem reach_of_access (g : GcIn) (pol : SSPolicy) (run : List Acc)
    (h1 : EdgeAccessesFollowEdges g.edges g.IsRoot run)
    (h2 : ImplicitAccessesHitRoots g.IsRoot run) (h3 : BoundsAccessesRetained g pol run) :
    ∀ (k : Nat) (a : Acc), run[k]? = some a → g.Live pol a.dst := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:191-195
theorem live_iff_exists_valid_run (g : GcIn) (pol : SSPolicy) (j : Nat) :
    g.Live pol j ↔
      ∃ run : List Acc, EdgeAccessesFollowEdges g.edges g.IsRoot run ∧
        ImplicitAccessesHitRoots g.IsRoot run ∧ BoundsAccessesRetained g pol run ∧
        ∃ a ∈ run, a.dst = j := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:130-133
theorem exists_valid_run_of_live (g : GcIn) (pol : SSPolicy) (j : Nat) (h : g.Live pol j) :
    ∃ run : List Acc, EdgeAccessesFollowEdges g.edges g.IsRoot run ∧
      ImplicitAccessesHitRoots g.IsRoot run ∧ BoundsAccessesRetained g pol run ∧
      ∃ a ∈ run, a.dst = j := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:891-893
theorem phantom_section_live :
    gcPhantom.secs[99]? = none ∧ gcPhantom.Live .precise 99 ∧
      RegistryKept gcPhantom .conservative 7 := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:297-299
theorem reach_secEdges_map (E : List (Nat × Nat)) (R : Nat → Prop) (sec f : Nat → Nat) :
    ∀ s, Reach (secEdges sec E) (secRoot sec R) s →
      Reach (secEdges (fun i => f (sec i)) E) (secRoot (fun i => f (sec i)) R) (f s) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:339-341
theorem unreferenced_item_kept_when_sharing_live_section :
    (∀ e ∈ itemEdges, e.2 ≠ 2) ∧ ¬ itemRoot 2 ∧ KeptItem secShared itemEdges itemRoot 2 ∧
      ¬ KeptItem secFine itemEdges itemRoot 2 ∧ ¬ ∃ f : Nat → Nat, ∀ i, secFine i = f (secShared i) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:359-360
theorem coarsening_nonvacuity :
    (∀ i, secShared i = secShared (secFine i)) ∧ KeptItem secFine itemEdges itemRoot 1 :=
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:479-481
theorem registry_precise_link_failure_conservative_kept :
    StartStopUndefined (gcReg [] false false) .precise 7 ∧
      RegistryKept (gcReg [] false false) .conservative 7 := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:494-499
theorem registry_precise_silent_shrink :
    (gcReg [(0, 1)] false false).Live .precise 1 ∧
      ¬ (gcReg [(0, 1)] false false).Live .precise 2 ∧
      ¬ RegistryKept (gcReg [(0, 1)] false false) .precise 7 ∧
      ¬ StartStopUndefined (gcReg [(0, 1)] false false) .precise 7 ∧
      RegistryKept (gcReg [(0, 1)] false false) .conservative 7 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:907-909
theorem empty_registry_kept_and_undefined (pol : SSPolicy) :
    (∀ j, gcEmptyReg.nameOf j ≠ some 7) ∧ RegistryKept gcEmptyReg pol 7 ∧
      StartStopUndefined gcEmptyReg pol 7 := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:542-544
theorem registry_nonvacuity :
    NoEdgeIntoName (gcReg [] false false) 7 ∧ (gcReg [] false false).nameOf 1 = some 7 ∧
      (∀ j, (gcReg [] false false).nameOf j = some 7 → ¬ (gcReg [] false false).IsRoot j) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:400-402
theorem live_iff_root_or_conservative_reference_of_noEdgeIntoName (g : GcIn) (pol : SSPolicy)
    (X j : Nat) (hN : NoEdgeIntoName g X) (hj : g.nameOf j = some X) :
    g.Live pol j ↔ g.IsRoot j ∨ (pol = .conservative ∧ ∃ i, g.Live pol i ∧ (i, X) ∈ g.ss) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:385-386
theorem conservative_registryKept_of_live_reference (g : GcIn) (X i : Nat)
    (hi : g.Live .conservative i) (hss : (i, X) ∈ g.ss) : RegistryKept g .conservative X := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:393-394
theorem registryKept_of_entries_rooted (g : GcIn) (pol : SSPolicy) (X : Nat)
    (h : ∀ j, g.nameOf j = some X → g.IsRoot j) : RegistryKept g pol X :=
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:440-441
theorem runPreserved_registryScan_iff_registryKept (g : GcIn) (pol : SSPolicy) (i X : Nat) :
    RunPreserved g pol (registryScan g i X) ↔ RegistryKept g pol X := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:870-871
theorem conservative_registryKept_nonvacuity :
    (gcReg [] false false).Live .conservative 0 ∧ (0, 7) ∈ (gcReg [] false false).ss :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:877-879
theorem registryKept_of_entries_rooted_nonvacuity :
    (∀ j, (gcReg [] true false).nameOf j = some 7 → (gcReg [] true false).IsRoot j) ∧
      (∀ j, (gcReg [] false true).nameOf j = some 7 → (gcReg [] false true).IsRoot j) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:513-515
theorem registry_keep_or_retain_kept_precise :
    RegistryKept (gcReg [] true false) .precise 7 ∧
      RegistryKept (gcReg [] false true) .precise 7 := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:527-534
theorem registry_iff_cex_edge_into_entry :
    ¬ NoEdgeIntoName (gcReg [(0, 1)] false false) 7 ∧
      (gcReg [(0, 1)] false false).nameOf 1 = some 7 ∧
      ¬ ((gcReg [(0, 1)] false false).Live .precise 1 ↔
        (gcReg [(0, 1)] false false).IsRoot 1 ∨
          ((SSPolicy.precise : SSPolicy) = .conservative ∧
            ∃ i, (gcReg [(0, 1)] false false).Live .precise i ∧
              (i, 7) ∈ (gcReg [(0, 1)] false false).ss)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:760-766
theorem registry_iff_cex_other_name :
    NoEdgeIntoName (gcReg [(0, 1)] false false) 9 ∧ (gcReg [(0, 1)] false false).nameOf 1 ≠ some 9 ∧
      ¬ ((gcReg [(0, 1)] false false).Live .precise 1 ↔
        (gcReg [(0, 1)] false false).IsRoot 1 ∨
          ((SSPolicy.precise : SSPolicy) = .conservative ∧
            ∃ i, (gcReg [(0, 1)] false false).Live .precise i ∧
              (i, 9) ∈ (gcReg [(0, 1)] false false).ss)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:732-734
theorem conservative_cex_dead_referencer :
    ¬ gcDeadRef.Live .conservative 1 ∧ (1, 7) ∈ gcDeadRef.ss ∧
      ¬ RegistryKept gcDeadRef .conservative 7 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:741-744
theorem conservative_cex_no_reference :
    (⟨(gcReg [] false false).secs, [], []⟩ : GcIn).Live .conservative 0 ∧
      ¬ (0, 7) ∈ (⟨(gcReg [] false false).secs, [], []⟩ : GcIn).ss ∧
      ¬ RegistryKept ⟨(gcReg [] false false).secs, [], []⟩ .conservative 7 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:751-753
theorem rooted_cex_unrooted :
    ¬ (∀ j, (gcReg [] false false).nameOf j = some 7 → (gcReg [] false false).IsRoot j) ∧
      ¬ RegistryKept (gcReg [] false false) .precise 7 :=
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:36-38
theorem mem_ssEdges_conservative (g : GcIn) (i j : Nat) :
    (i, j) ∈ g.ssEdges .conservative ↔
      ∃ X, (i, X) ∈ g.ss ∧ j < g.secs.length ∧ g.nameOf j = some X := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:561
theorem survives_iff_linkReach (p : Prog2) (i : Nat) : p.Survives i ↔ p.LinkReach i :=
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:551
theorem compiled_of_linkReach (p : Prog2) (i : Nat) (h : p.LinkReach i) : p.compiled i = true := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:601-603
theorem survives_iff_compileKept_and_linkReach_or_retain (p : Prog2) (i : Nat) (s : Static)
    (hs : p.statics[i]? = some s) :
    p.Survives i ↔ (s.cref = true ∨ s.cused = true) ∧ (p.LinkReach i ∨ s.retain = true) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:714-718
theorem survives_conjunction_cex_without_lookup :
    (Prog2.mk [] []).statics[0]? ≠ some stUsedRetained ∧
      ¬ ((Prog2.mk [] []).Survives 0 ↔
        (stUsedRetained.cref = true ∨ stUsedRetained.cused = true) ∧
          ((Prog2.mk [] []).LinkReach 0 ∨ stUsedRetained.retain = true)) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:703-707
theorem twoStage_nonvacuity :
    (Prog2.mk [stMain, stUsedRetained] []).statics[1]? = some stUsedRetained ∧
      (Prog2.mk [stMain, stUsedRetained] []).Survives 1 ∧
      (Prog2.mk [stMain, stUsedRetained] []).CompiledPath 1 ∧
      (Prog2.mk [stMain, stUsedRetained] []).Survives 0 :=
```

`Prog2.objRootB p i` is the Boolean object-level root test used in the hypothesis `hR` of `linkReach_closed`: it is `true` when the compiler stage keeps static `i` (`p.compiled i`) and the record of static `i` has `lroot` or `retain` set, and `false` otherwise (in particular when `p` has no static `i`).

```lean
-- lean/ToyRelroGc/Gc/Results.lean:617-620
def Prog2.objRootB (p : Prog2) (i : Nat) : Bool :=
  p.compiled i && match p.statics[i]? with
    | some s => s.lroot || s.retain
    | none => false
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:622-625
theorem linkReach_closed (p : Prog2) (S : Nat → Bool)
    (hR : ∀ i < p.statics.length, p.objRootB i = true → S i = true)
    (hE : ∀ e ∈ p.objEdges, S e.1 = true → S e.2 = true) :
    ∀ j, p.LinkReach j → S j = true := by
```

### Witness and counterexample statements (verbatim)

```lean
-- lean/ToyRelroGc/Relro/Results.lean:49-51
theorem twoPhase_nonvacuity :
    RelocSlotsWritable goodCfg ∧ 1 = goodCfg.relocs.length ∧ ProtCoversRelro goodCfg ∧
      ProtAvoidsMut goodCfg := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:58-60
theorem twoPhase_cex_slot_not_writable :
    ¬ RelocSlotsWritable cfgSlotRo ∧ 1 = cfgSlotRo.relocs.length ∧ ProtCoversRelro cfgSlotRo ∧
      ProtAvoidsMut cfgSlotRo ∧ ¬ TwoPhaseGuarantees cfgSlotRo sa0 [] 1 := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:75-78
theorem twoPhase_cex_protect_before_last_reloc :
    RelocSlotsWritable cfgTwoRelro ∧ (1 : Nat) ≠ cfgTwoRelro.relocs.length ∧
      ProtCoversRelro cfgTwoRelro ∧ ProtAvoidsMut cfgTwoRelro ∧
      ¬ TwoPhaseGuarantees cfgTwoRelro sa0 [] 1 := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:85-88
theorem twoPhase_cex_protect_after_entry :
    RelocSlotsWritable goodCfg ∧ (2 : Nat) ≠ goodCfg.relocs.length ∧
      ProtCoversRelro goodCfg ∧ ProtAvoidsMut goodCfg ∧
      ¬ TwoPhaseGuarantees goodCfg sa0 [.write 0 9] 2 := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:98-100
theorem twoPhase_cex_prot_misses_relro :
    RelocSlotsWritable cfgNoProt ∧ 1 = cfgNoProt.relocs.length ∧ ¬ ProtCoversRelro cfgNoProt ∧
      ProtAvoidsMut cfgNoProt ∧ ¬ TwoPhaseGuarantees cfgNoProt sa0 [.write 0 9] 1 := by
```

```lean
-- lean/ToyRelroGc/Relro/Results.lean:110-112
theorem twoPhase_cex_prot_covers_mut :
    RelocSlotsWritable cfgProtMut ∧ 1 = cfgProtMut.relocs.length ∧ ProtCoversRelro cfgProtMut ∧
      ¬ ProtAvoidsMut cfgProtMut ∧ ¬ TwoPhaseGuarantees cfgProtMut sa0 [.write 1 9] 1 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:252-260
theorem placement_nonvacuity :
    (symReloc 0 0 ∈ cfgSlotRo.relocs ∧ cfgSlotRo.kinds[(symReloc 0 0).slot]? = some .ro) ∧
      (symReloc 0 0 ∈ cfgMutReloc.relocs ∧ RelocSlotsWritable cfgMutReloc ∧
        cfgMutReloc.kinds[(symReloc 0 0).slot]? = some .mutable ∧ ProtAvoidsMut cfgMutReloc) ∧
      (symReloc 0 0 ∈ goodCfg.relocs ∧ RelocSlotsWritable goodCfg ∧
        goodCfg.kinds[(symReloc 0 0).slot]? = some .relro ∧ ProtCoversRelro goodCfg ∧
        ProtAvoidsMut goodCfg ∧
        (∀ r' ∈ goodCfg.relocs, r'.slot ≠ (symReloc 0 0).slot →
          mapWr goodCfg.kinds r'.slot = true)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:567-569
theorem pic_rodata_cex_relro_slot :
    symReloc 0 0 ∈ goodCfg.relocs ∧ goodCfg.kinds[(symReloc 0 0).slot]? ≠ some .ro ∧
      LoadOk (trace goodCfg sa0 (twoPhase goodCfg [])) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:575-582
theorem placement_iff_cex_not_dynamic :
    ¬ symReloc 0 0 ∈ (linkResolve sa0 cfgSlotRo).relocs ∧
      (∀ r' ∈ (linkResolve sa0 cfgSlotRo).relocs, r'.slot ≠ (symReloc 0 0).slot →
        mapWr (linkResolve sa0 cfgSlotRo).kinds r'.slot = true) ∧
      ProtCoversRelro (linkResolve sa0 cfgSlotRo) ∧ ProtAvoidsMut (linkResolve sa0 cfgSlotRo) ∧
      ¬ ((LoadOk (trace (linkResolve sa0 cfgSlotRo) sa0 (twoPhase (linkResolve sa0 cfgSlotRo) [])) ∧
          WriteFaultsAfter (linkResolve sa0 cfgSlotRo) sa0 (symReloc 0 0).slot) ↔
        (linkResolve sa0 cfgSlotRo).kinds[(symReloc 0 0).slot]? = some .relro) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:271-284
theorem placement_iff_cex_other_reloc :
    symReloc 0 0 ∈ (⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩
        : Cfg).relocs ∧
      ¬ (∀ r' ∈ (⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩
          : Cfg).relocs, r'.slot ≠ (symReloc 0 0).slot →
            mapWr [.relro, .ro] r'.slot = true) ∧
      ProtCoversRelro ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩ ∧
      ProtAvoidsMut ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩ ∧
      ¬ ((LoadOk (trace ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0], rangeMask 0 1, [], 0⟩
            sa0 (twoPhase ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0],
              rangeMask 0 1, [], 0⟩ [])) ∧
          WriteFaultsAfter ⟨[.relro, .ro], fun _ => 0, [symReloc 0 0, symReloc 1 0],
            rangeMask 0 1, [], 0⟩ sa0 (symReloc 0 0).slot) ↔
        [Kind.relro, Kind.ro][(symReloc 0 0).slot]? = some .relro) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:294-301
theorem placement_iff_cex_no_cover :
    symReloc 0 0 ∈ cfgNoProt.relocs ∧
      (∀ r' ∈ cfgNoProt.relocs, r'.slot ≠ (symReloc 0 0).slot →
        mapWr cfgNoProt.kinds r'.slot = true) ∧
      ¬ ProtCoversRelro cfgNoProt ∧ ProtAvoidsMut cfgNoProt ∧
      ¬ ((LoadOk (trace cfgNoProt sa0 (twoPhase cfgNoProt [])) ∧
          WriteFaultsAfter cfgNoProt sa0 (symReloc 0 0).slot) ↔
        cfgNoProt.kinds[(symReloc 0 0).slot]? = some .relro) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:317-324
theorem placement_iff_cex_cover_mut :
    symReloc 0 0 ∈ cfgMutCovered.relocs ∧
      (∀ r' ∈ cfgMutCovered.relocs, r'.slot ≠ (symReloc 0 0).slot →
        mapWr cfgMutCovered.kinds r'.slot = true) ∧
      ProtCoversRelro cfgMutCovered ∧ ¬ ProtAvoidsMut cfgMutCovered ∧
      ¬ ((LoadOk (trace cfgMutCovered sa0 (twoPhase cfgMutCovered [])) ∧
          WriteFaultsAfter cfgMutCovered sa0 (symReloc 0 0).slot) ↔
        cfgMutCovered.kinds[(symReloc 0 0).slot]? = some .relro) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:99-102
theorem bindings_nonvacuity :
    EagerRelroOrLazy mixedCfg [(0, 0), (1, 1)] ∧
      (∀ b ∈ [((0 : Nat), (0 : Sym)), (1, 1)], CallWorks mixedCfg sa0 b.1 b.2) ∧
      ProtCoversRelro mixedCfg :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:114-119
theorem bindings_iff_cex_eager_outside_relro :
    ¬ EagerRelroOrLazy eagerMutCfg [(0, 0)] ∧
      (∀ b ∈ [((0 : Nat), (0 : Sym))], CallWorks eagerMutCfg sa0 b.1 b.2) ∧
      ProtCoversRelro eagerMutCfg ∧
      ¬ ((∀ b ∈ [((0 : Nat), (0 : Sym))], WriteFaultsAfter eagerMutCfg sa0 b.1) ↔
        (∀ b ∈ [((0 : Nat), (0 : Sym))], EagerBound eagerMutCfg b.1 b.2)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:140-145
theorem bindings_iff_cex_call_faults :
    EagerRelroOrLazy lazyRelroCfg [(0, 0)] ∧
      ¬ (∀ b ∈ [((0 : Nat), (0 : Sym))], CallWorks lazyRelroCfg sa0 b.1 b.2) ∧
      ProtCoversRelro lazyRelroCfg ∧
      ¬ ((∀ b ∈ [((0 : Nat), (0 : Sym))], WriteFaultsAfter lazyRelroCfg sa0 b.1) ↔
        (∀ b ∈ [((0 : Nat), (0 : Sym))], EagerBound lazyRelroCfg b.1 b.2)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:165-173
theorem bindings_iff_cex_no_cover :
    EagerRelroOrLazy { eagerCfg with prot := fun _ => false } [(0, 0)] ∧
      (∀ b ∈ [((0 : Nat), (0 : Sym))],
        CallWorks { eagerCfg with prot := fun _ => false } sa0 b.1 b.2) ∧
      ¬ ProtCoversRelro { eagerCfg with prot := fun _ => false } ∧
      ¬ ((∀ b ∈ [((0 : Nat), (0 : Sym))],
            WriteFaultsAfter { eagerCfg with prot := fun _ => false } sa0 b.1) ↔
        (∀ b ∈ [((0 : Nat), (0 : Sym))],
            EagerBound { eagerCfg with prot := fun _ => false } b.1 b.2)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:90-92
theorem bindings_callWorks_nonvacuity :
    EagerRelroOrLazyMut mixedCfg [(0, 0), (1, 1)] ∧ RelocSlotsWritable mixedCfg ∧
      ProtAvoidsMut mixedCfg :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:212-214
theorem callWorks_cex_lazy_in_relro :
    ¬ EagerRelroOrLazyMut lazyRelroCfg [(0, 0)] ∧ RelocSlotsWritable lazyRelroCfg ∧
      ProtAvoidsMut lazyRelroCfg ∧ ¬ CallWorks lazyRelroCfg sa0 0 0 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:220-228
theorem callWorks_cex_slot_not_writable :
    EagerRelroOrLazyMut ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ [(0, 0)] ∧
      ¬ RelocSlotsWritable ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ ∧
      ProtAvoidsMut ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ ∧
      ¬ CallWorks ⟨[.relro, .ro], fun _ => 0, [bindReloc 0 0, symReloc 1 0],
        rangeMask 0 1, [], 0⟩ sa0 0 0 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:202-206
theorem callWorks_cex_cover_mut :
    EagerRelroOrLazyMut { lazyMutCfg with prot := rangeMask 0 1 } [(0, 0)] ∧
      RelocSlotsWritable { lazyMutCfg with prot := rangeMask 0 1 } ∧
      ¬ ProtAvoidsMut { lazyMutCfg with prot := rangeMask 0 1 } ∧
      ¬ CallWorks { lazyMutCfg with prot := rangeMask 0 1 } sa0 0 0 := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:595-597
theorem downDown_avoidsMut_cex_relroIs :
    ¬ RelroIs [.relro, .mutable] 0 4 ∧ NoMutIn [.relro, .mutable] (alignDown 2 0) 0 ∧
      ¬ AvoidsMut [.relro, .mutable] (roundedMask .downDown 2 0 4) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:373-375
theorem downDown_coversRelro_iff_cex_relroIs :
    ¬ RelroIs layoutRelro3 0 2 ∧ (0 : Nat) < 2 ∧
      ¬ (CoversRelro layoutRelro3 (roundedMask .downDown 2 0 2) ↔ 2 % 2 = 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:366-368
theorem downDown_coversRelro_iff_cex_empty :
    RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ (CoversRelro [.mutable] (roundedMask .downDown 2 1 1) ↔ 1 % 2 = 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:379-381
theorem downUp_coversRelro_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs layoutRelro3 0 3 ∧
      ¬ CoversRelro layoutRelro3 (roundedMask .downUp 0 0 3) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:602-604
theorem downUp_coversRelro_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs [.relro, .relro] 0 0 ∧
      ¬ CoversRelro [.relro, .relro] (roundedMask .downUp 2 0 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:385-388
theorem downUp_avoidsMut_iff_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs layoutMutRelro 1 2 ∧ (1 : Nat) < 2 ∧
      ¬ (AvoidsMut layoutMutRelro (roundedMask .downUp 0 1 2) ↔
        NoMutIn layoutMutRelro (alignDown 0 1) 1 ∧ NoMutIn layoutMutRelro 2 (alignUp 0 2)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:608-611
theorem downUp_avoidsMut_iff_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs [.relro, .mutable] 0 2 ∧ (0 : Nat) < 2 ∧
      ¬ (AvoidsMut [.relro, .mutable] (roundedMask .downUp 2 0 2) ↔
        NoMutIn [.relro, .mutable] (alignDown 2 0) 0 ∧ NoMutIn [.relro, .mutable] 2 (alignUp 2 2)) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:394-397
theorem downUp_avoidsMut_iff_cex_empty :
    (0 : Nat) < 2 ∧ RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ (AvoidsMut [.mutable] (roundedMask .downUp 2 1 1) ↔
        NoMutIn [.mutable] (alignDown 2 1) 1 ∧ NoMutIn [.mutable] 1 (alignUp 2 1)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:623-626
theorem exists_pageGranular_iff_cex_pageZero :
    ¬ ((0 : Nat) < 0) ∧ RelroIs [.relro, .mutable] 0 1 ∧ 0 < 1 ∧
      ¬ ((∃ m, PageGranular 0 m ∧ CoversRelro [.relro, .mutable] m ∧ AvoidsMut [.relro, .mutable] m) ↔
        NoMutIn [.relro, .mutable] (alignDown 0 0) 0 ∧ NoMutIn [.relro, .mutable] 1 (alignUp 0 1)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:639-642
theorem exists_pageGranular_iff_cex_relroIs :
    0 < 2 ∧ ¬ RelroIs layoutRelro3Mut 0 2 ∧ 0 < 2 ∧
      ¬ ((∃ m, PageGranular 2 m ∧ CoversRelro layoutRelro3Mut m ∧ AvoidsMut layoutRelro3Mut m) ↔
        NoMutIn layoutRelro3Mut (alignDown 2 0) 0 ∧ NoMutIn layoutRelro3Mut 2 (alignUp 2 2)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:631-634
theorem exists_pageGranular_iff_cex_empty :
    0 < 2 ∧ RelroIs [.mutable] 1 1 ∧ ¬ ((1 : Nat) < 1) ∧
      ¬ ((∃ m, PageGranular 2 m ∧ CoversRelro [.mutable] m ∧ AvoidsMut [.mutable] m) ↔
        NoMutIn [.mutable] (alignDown 2 1) 1 ∧ NoMutIn [.mutable] 1 (alignUp 2 1)) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:648-651
theorem order_cex_not_perm :
    ¬ [symReloc 0 0].Perm [] ∧ (∀ r ∈ [symReloc 0 0], r.AddressOnly) ∧
      ([symReloc 0 0].map Reloc.slot).Nodup ∧
      applyAll sa0 [symReloc 0 0] (fun _ => 0) ≠ applyAll sa0 [] (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:515-520
theorem resolver_reads_unrelocated_slot_order_dependent :
    [rAddr0, rRes1].Perm [rRes1, rAddr0] ∧ ([rAddr0, rRes1].map Reloc.slot).Nodup ∧
      ¬ (∀ r ∈ [rAddr0, rRes1], r.AddressOnly) ∧
      applyAll sa0 [rAddr0, rRes1] (fun _ => 0) ≠ applyAll sa0 [rRes1, rAddr0] (fun _ => 0) ∧
      applyAll sa0 [rAddr0, rRes1] (fun _ => 0) 1 = 100 ∧
      applyAll sa0 [rRes1, rAddr0] (fun _ => 0) 1 = 0 := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:530-535
theorem addressOnly_same_slot_order_dependent :
    [symReloc 0 0, symReloc 0 1].Perm [symReloc 0 1, symReloc 0 0] ∧
      (∀ r ∈ [symReloc 0 0, symReloc 0 1], r.AddressOnly) ∧
      ¬ ([symReloc 0 0, symReloc 0 1].map Reloc.slot).Nodup ∧
      applyAll sa0 [symReloc 0 0, symReloc 0 1] (fun _ => 0) ≠
        applyAll sa0 [symReloc 0 1, symReloc 0 0] (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:613-619
theorem nonAddressOnly_first_group_order_dependent :
    ¬ (∀ r ∈ [rAddr0, rRes1], r.AddressOnly) ∧ ([rAddr0, rRes1].map Reloc.slot).Nodup ∧
      (∀ r ∈ ([] : List Reloc), r.ReadsOnly (fun a => a ∉ ([] : List Reloc).map Reloc.slot)) ∧
      (([] : List Reloc).map Reloc.slot).Nodup ∧
      [rRes1, rAddr0].Perm [rAddr0, rRes1] ∧ ([] : List Reloc).Perm [] ∧
      applyAll sa0 ([rRes1, rAddr0] ++ []) (fun _ => 0) ≠
        applyAll sa0 ([rAddr0, rRes1] ++ []) (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:628-635
theorem addressOnly_first_group_same_slot_order_dependent :
    (∀ r ∈ [symReloc 0 0, symReloc 0 1], r.AddressOnly) ∧
      ¬ ([symReloc 0 0, symReloc 0 1].map Reloc.slot).Nodup ∧
      (∀ r ∈ ([] : List Reloc), r.ReadsOnly (fun a => a ∉ ([] : List Reloc).map Reloc.slot)) ∧
      (([] : List Reloc).map Reloc.slot).Nodup ∧
      [symReloc 0 1, symReloc 0 0].Perm [symReloc 0 0, symReloc 0 1] ∧ ([] : List Reloc).Perm [] ∧
      applyAll sa0 ([symReloc 0 1, symReloc 0 0] ++ []) (fun _ => 0) ≠
        applyAll sa0 ([symReloc 0 0, symReloc 0 1] ++ []) (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:550-557
theorem resolvers_read_resolver_slot_order_dependent :
    (∀ r ∈ ([] : List Reloc), r.AddressOnly) ∧ (([] : List Reloc).map Reloc.slot).Nodup ∧
      ¬ (∀ r ∈ [symReloc 1 0, rRes2of1],
          r.ReadsOnly (fun a => a ∉ [symReloc 1 0, rRes2of1].map Reloc.slot)) ∧
      ([symReloc 1 0, rRes2of1].map Reloc.slot).Nodup ∧
      ([] : List Reloc).Perm [] ∧ [rRes2of1, symReloc 1 0].Perm [symReloc 1 0, rRes2of1] ∧
      applyAll sa0 ([] ++ [rRes2of1, symReloc 1 0]) (fun _ => 0) ≠
        applyAll sa0 ([] ++ [symReloc 1 0, rRes2of1]) (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:573-579
theorem resolver_overwrites_addressOnly_slot_order_dependent :
    (∀ r ∈ [rAddr0], r.AddressOnly) ∧ ([rAddr0].map Reloc.slot).Nodup ∧
      ¬ (∀ r ∈ [rConst0, rRes1], r.ReadsOnly (fun a => a ∉ [rConst0, rRes1].map Reloc.slot)) ∧
      ([rConst0, rRes1].map Reloc.slot).Nodup ∧
      [rAddr0].Perm [rAddr0] ∧ [rRes1, rConst0].Perm [rConst0, rRes1] ∧
      applyAll sa0 ([rAddr0] ++ [rRes1, rConst0]) (fun _ => 0) ≠
        applyAll sa0 ([rAddr0] ++ [rConst0, rRes1]) (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Relro/Results2.lean:594-601
theorem resolvers_same_slot_order_dependent :
    (∀ r ∈ ([] : List Reloc), r.AddressOnly) ∧ (([] : List Reloc).map Reloc.slot).Nodup ∧
      (∀ r ∈ [symReloc 0 0, symReloc 0 1],
        r.ReadsOnly (fun a => a ∉ [symReloc 0 0, symReloc 0 1].map Reloc.slot)) ∧
      ¬ ([symReloc 0 0, symReloc 0 1].map Reloc.slot).Nodup ∧
      ([] : List Reloc).Perm [] ∧ [symReloc 0 1, symReloc 0 0].Perm [symReloc 0 0, symReloc 0 1] ∧
      applyAll sa0 ([] ++ [symReloc 0 1, symReloc 0 0]) (fun _ => 0) ≠
        applyAll sa0 ([] ++ [symReloc 0 0, symReloc 0 1]) (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:661-666
theorem resolverOrder_cex_not_permA :
    (∀ r ∈ [rAddr0], r.AddressOnly) ∧ ([rAddr0].map Reloc.slot).Nodup ∧
      (∀ r ∈ ([] : List Reloc), r.ReadsOnly (fun a => a ∉ ([] : List Reloc).map Reloc.slot)) ∧
      (([] : List Reloc).map Reloc.slot).Nodup ∧ ¬ ([] : List Reloc).Perm [rAddr0] ∧
      ([] : List Reloc).Perm [] ∧
      applyAll sa0 ([] ++ []) (fun _ => 0) ≠ applyAll sa0 ([rAddr0] ++ []) (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:677-682
theorem resolverOrder_cex_not_permR :
    (∀ r ∈ ([] : List Reloc), r.AddressOnly) ∧ (([] : List Reloc).map Reloc.slot).Nodup ∧
      (∀ r ∈ [rAddr0], r.ReadsOnly (fun a => a ∉ [rAddr0].map Reloc.slot)) ∧
      ([rAddr0].map Reloc.slot).Nodup ∧ ([] : List Reloc).Perm [] ∧
      ¬ ([] : List Reloc).Perm [rAddr0] ∧
      applyAll sa0 ([] ++ []) (fun _ => 0) ≠ applyAll sa0 ([] ++ [rAddr0]) (fun _ => 0) := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:213-217
theorem gcSoundness_nonvacuity (pol : SSPolicy) :
    EdgeAccessesFollowEdges (gcPair [(0, 1)]).edges (gcPair [(0, 1)]).IsRoot
        [.implicit 0, .edge 0 1] ∧
      ImplicitAccessesHitRoots (gcPair [(0, 1)]).IsRoot [.implicit 0, .edge 0 1] ∧
      BoundsAccessesRetained (gcPair [(0, 1)]) pol [.implicit 0, .edge 0 1] := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:799-805
theorem gcSoundness_bounds_nonvacuity :
    EdgeAccessesFollowEdges (gcReg [] false false).edges (gcReg [] false false).IsRoot
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] ∧
      ImplicitAccessesHitRoots (gcReg [] false false).IsRoot
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] ∧
      BoundsAccessesRetained (gcReg [] false false) .conservative
        [.implicit 0, .bounds 0 7 1, .bounds 0 7 2] := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:271-275
theorem gcSoundness_cex_edge_access_without_edge (pol : SSPolicy) :
    ¬ EdgeAccessesFollowEdges (gcPair []).edges (gcPair []).IsRoot [.implicit 0, .edge 0 1] ∧
      ImplicitAccessesHitRoots (gcPair []).IsRoot [.implicit 0, .edge 0 1] ∧
      BoundsAccessesRetained (gcPair []) pol [.implicit 0, .edge 0 1] ∧
      ¬ RunPreserved (gcPair []) pol [.implicit 0, .edge 0 1] := by
```

```lean
-- lean/ToyRelroGc/Gc/Results.lean:250-254
theorem gcSoundness_cex_implicit_access_to_nonroot (pol : SSPolicy) :
    EdgeAccessesFollowEdges (gcPair []).edges (gcPair []).IsRoot [.implicit 1] ∧
      ¬ ImplicitAccessesHitRoots (gcPair []).IsRoot [.implicit 1] ∧
      BoundsAccessesRetained (gcPair []) pol [.implicit 1] ∧
      ¬ RunPreserved (gcPair []) pol [.implicit 1] := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:840-845
theorem gcSoundness_cex_bounds_access_unretained :
    EdgeAccessesFollowEdges (gcReg [] false false).edges (gcReg [] false false).IsRoot
        [.implicit 0, .bounds 0 7 1] ∧
      ImplicitAccessesHitRoots (gcReg [] false false).IsRoot [.implicit 0, .bounds 0 7 1] ∧
      ¬ BoundsAccessesRetained (gcReg [] false false) .precise [.implicit 0, .bounds 0 7 1] ∧
      ¬ RunPreserved (gcReg [] false false) .precise [.implicit 0, .bounds 0 7 1] := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:702-704
theorem coarsening_cex_refinement :
    (¬ ∃ f : Nat → Nat, ∀ i, secFine i = f (secShared i)) ∧
      KeptItem secShared itemEdges itemRoot 2 ∧ ¬ KeptItem secFine itemEdges itemRoot 2 :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:694-696
theorem coarsening_cex_not_kept :
    (∀ i, secFine i = (fun s => s) (secFine i)) ∧ ¬ KeptItem secFine itemEdges itemRoot 2 ∧
      ¬ KeptItem secFine itemEdges itemRoot 2 :=
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:710-714
theorem precise_drops_cex_edge_into_entry :
    ¬ NoEdgeIntoName (gcReg [(0, 1)] false false) 7 ∧
      (∀ j, (gcReg [(0, 1)] false false).nameOf j = some 7 → ¬ (gcReg [(0, 1)] false false).IsRoot j) ∧
      ¬ (∀ j, (gcReg [(0, 1)] false false).nameOf j = some 7 →
        ¬ (gcReg [(0, 1)] false false).Live .precise j) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:720-723
theorem precise_drops_cex_rooted_entry :
    NoEdgeIntoName (gcReg [] true false) 7 ∧
      ¬ (∀ j, (gcReg [] true false).nameOf j = some 7 → ¬ (gcReg [] true false).IsRoot j) ∧
      ¬ (∀ j, (gcReg [] true false).nameOf j = some 7 → ¬ (gcReg [] true false).Live .precise j) := by
```

```lean
-- lean/ToyRelroGc/Witnesses.lean:774-781
theorem registryKept_iff_cex_edges_into_entries :
    ¬ NoEdgeIntoName (gcReg [(0, 1), (0, 2)] false false) 7 ∧
      ¬ (RegistryKept (gcReg [(0, 1), (0, 2)] false false) .precise 7 ↔
        ∀ j, (gcReg [(0, 1), (0, 2)] false false).nameOf j = some 7 →
          (gcReg [(0, 1), (0, 2)] false false).IsRoot j ∨
            ((SSPolicy.precise : SSPolicy) = .conservative ∧
              ∃ i, (gcReg [(0, 1), (0, 2)] false false).Live .precise i ∧
                (i, 7) ∈ (gcReg [(0, 1), (0, 2)] false false).ss)) := by
```

### Modeling-bridge notes (derived (modeling bridge))

These connect the toy to documented behaviour. They are not established by the Lean proofs; full quotes are in the
cards' prior-art entries.

* **Relocate, then protect.** glibc 2.40 `_dl_relocate_object` calls `ELF_DYNAMIC_RELOCATE` (elf/dl-reloc.c line 301)
  before `_dl_protect_relro` (lines 348-349) for one object; this matches the shape of `twoPhase`. Basis: source.
* **Rounding.** glibc 2.40 `_dl_protect_relro` (elf/dl-reloc.c lines 353-370), musl 1.2.5 (ldso/dynlink.c lines 734-735)
  and FreeBSD rtld (libexec/rtld-elf/rtld.c lines 1701-1703) round both ends of the RELRO range down (the toy's
  `downDown`); Android Bionic (linker/linker_phdr.cpp lines 915-916) rounds the start down and the end up (the toy's
  `downUp`). The GNU ld manual documents `DATA_SEGMENT_RELRO_END`, which pads so that the RELRO end is aligned to the
  common page size, and warns that a `common-page-size` smaller than the system page size "will render this
  protection ineffective". The Bionic source quotes a description of the start-of-region hazard. Whether a given
  linker ever places mutable data on the first RELRO page below the RELRO start is not examined here.
* **Placement of constants with relocations.** LLVM 19.1.0 classifies a constant whose initializer needs a dynamic
  relocation as `ReadOnlyWithRel` (prefix `.data.rel.ro`) and returns read-only data for the static, ROPI and RWPI
  relocation models or when no dynamic relocation is needed; R2a and R2d state the toy counterpart.
* **Eager versus lazy binding.** GNU ld documents `-z now` versus `-z lazy` (default lazy binding); lld documents
  `DF_BIND_NOW`; a practitioner write-up describes partial RELRO (`.got` protected) and full RELRO (`-z relro -z now`,
  `.got.plt` protected, lazy binding disabled). R3a–R3c state the toy counterpart.
* **Relocation order.** Bernstein's read/write-set conditions underlie R5a and R5c. Within one relocation table, glibc
  2.40 `elf/do-rel.h` applies `IRELATIVE` entries in a second pass after the other entries; the toy's `A ++ R` order has
  this shape. Ordering across tables and objects is not modeled, and no claim is made about any loader's global order.
* **Start/stop retention.** GNU ld 2.42 documents the retaining effect of `__start_SECNAME`/`__stop_SECNAME` references
  (for C-identifier names and linker-synthesized bounds) and `-z start-stop-gc` (added in 2.37) to disable it; lld
  documents `-z start-stop-gc` as its default. The toy's `conservative` and `precise` policies correspond to these two
  behaviours.
* **Roots.** GNU ld documents the entry symbol, symbols undefined on the command line, symbols referenced by dynamic
  objects, `KEEP`, and `SHF_GNU_RETAIN` as reasons a section is kept; the toy has one flag per class.
* **Two-stage retention.** GCC 11 documents `used` (emitted even if unreferenced) and `retain` (saved from linker GC) as
  separate attributes; Clang documents that `retain` has no effect if the compiler does not emit the definition and is
  typically combined with `used`; the LLVM LangRef documents `@llvm.used` (compiler, assembler and linker) versus
  `@llvm.compiler.used` (compiler only); the Rust Reference documents that `#[used]` keeps a static in the object file
  while "the linker, however, is still free to remove it". R8a and R8b state the toy counterpart.

## Boundaries

### Non-claims (read first)

Cross-cutting non-claims:

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The RELRO model and the section-GC model are separate; nothing here establishes or refutes how section GC affects RELRO segment boundaries, page alignment, or the retention of statics placed in `.data.rel.ro` (not examined).
* Claims about loader runs quantify over the timelines produced by the generators `timeline` and `twoPhase` (relocations in list order, one `protect` event), and lazy binding is checked for the one-operation program `[call x]` (`CallWorks`); other schedules and programs are not covered.
* Each `tight` entry is witnessed in the stated class of small toy instances; it does not show that every real system violating the hypothesis misbehaves.
* The toy tracks write permission alone; read and execute permission are not modeled.

Non-claims of each result (identical to the card lists under Findings):

**R1** (`twoPhaseGuarantees_of_slotsWritable_of_protectAfterRelocs_of_covers_of_avoids`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The claim is for timelines produced by the generator timeline (relocations in list order, exactly one protect event inserted at position k). Several protect calls, several objects relocated one after another, concurrent threads, and permission changes requested by the program after entry are not modeled.
* Integrity here means that every program write to a RELRO byte faults. It says nothing about reads, about writes by the loader after entry (lazy binding is result R3), or about values written before protect. TwoPhaseGuarantees records the memory at protect and the outcomes of program writes; it states no invariance of memory contents across later program states, and writes by anything other than the program (debuggers, devices) are not modeled.
* It does not say how a real linker decides which bytes are RELRO, nor how protect is computed from page rounding (results R4a-R4g).
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The countermodels show each hypothesis is tight in this toy (loader inputs of at most two bytes); they do not show that every real loader violating a hypothesis is exploitable.

**R2a** (`pic_rodata_slot_load_faults`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Code bytes and unmapped addresses also fault in the toy (mapWr is false for them), but this card states the .rodata case alone.
* The toy has no mechanism that makes read-only pages temporarily writable during relocation (text relocations); the claim neither establishes nor refutes anything about loaders that have one.
* This applies to slots written by a dynamic relocation (r ∈ c.relocs). Position-independent encodings that need no dynamic relocation (for example PC-relative offsets, matching the !C->needsDynamicRelocation() case quoted in the prior art) have no counterpart in c.relocs, so they are outside this result.
* With link-time-resolved addresses (no dynamic relocation) a .rodata slot loads: see the positive control linkResolved_rodata_loadOk_writeFaultsAfter_and_image. In that theorem the load-time symbol table saR is arbitrary: linkResolve saL c bakes applyAll saL c.relocs c.init into the image and empties relocs, so loading never reads saR, and the theorem neither checks nor guarantees that load-time addresses agree with saL. Loading a link-resolved image at a different base address without relocation is not modeled.

**R2d** (`pic_loadOk_and_writeFaultsAfter_iff_relro`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* "RELRO" in this card is the toy kind relro together with H3 and H4; the equivalence is relative to those assumptions about protect, not a statement about which ELF sections a real linker protects.
* Under link-time-resolved addresses the classification changes (.rodata loads: linkResolved_rodata_loadOk_writeFaultsAfter_and_image); the card applies to relocations applied by the loader.
* This applies to slots written by a dynamic relocation (r ∈ c.relocs). Position-independent encodings that need no dynamic relocation (for example PC-relative offsets, matching the !C->needsDynamicRelocation() case quoted in the prior art) have no counterpart in c.relocs, so they are outside this result.
* The one-directional auxiliary lemmas pic_data_slot_loads_and_write_succeeds (mutable slot: load succeeds, later writes succeed; hypotheses H1, H4) and pic_relro_slot_loads_and_writeFaultsAfter (RELRO slot: load succeeds, writes fault; hypotheses H1, H3) are stated for a relocated slot r.slot with r ∈ c.relocs. That membership restricts the statements to relocated slots and is harmless: their conclusions hold for every byte of the given kind (the proofs do not use it).

**R3a** (`lazyBound_not_callWorks_and_writeFaultsAfter`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It does not say lazy binding is insecure in every threat model; integrity here is the toy's per-write faulting, and the attacker is arbitrary program writes after entry.
* CallWorks checks the isolated one-operation program [call x] executed immediately at entry, with no preceding program operation; later calls, re-binding and multi-operation programs are not covered.
* Escape hatches not ruled out by this impossibility, none of which the toy models: (a) a loader that changes permissions around each lazy binding; (b) hardware privilege or protection-domain separation giving the resolver write access that ordinary program writes lack; (c) non-caching lazy resolution that resolves the target on each call without writing x. The toy's resolver writes x with the program's own permissions.
* This impossibility concerns one lazily bound slot. It does not say that partial RELRO leaves eagerly bound slots (such as non-PLT GOT entries or .data.rel.ro) unprotected.

**R3b** (`bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The forward direction (protection implies eager) goes through the lazy-binding semantics, by lazyBound_not_callWorks_and_writeFaultsAfter; it uses no placement of lazy slots and no hypothesis that protect avoids mutable bytes. The backward direction uses the RELRO placement of eager slots and H3.
* For a list B that mixes eager and lazy bindings, both sides are false. This does not mean that the eager slots of B lose protection: for an eager binding b of B, the theorem applied to the singleton list [b] (whose hypotheses follow from those for B) gives post-entry write protection of b's slot.
* CallWorks checks the isolated one-operation program [call x] executed immediately at entry; in a multi-operation program an earlier write to a writable lazy slot can redirect even the first call through it (partial_relro_lazy_slot_write_redirects_call).
* It does not state that real linkers use this placement for every binding slot; see the prior-art entries for what is documented.

**R3c** (`bindings_callWorks_of_eagerRelroOrLazyMut`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* CallWorks checks the isolated one-operation program [call x] executed immediately at entry, with no preceding program operation; later calls are not covered. In a multi-operation program an earlier write to a writable lazy slot overwrites the stub and redirects even the first call through that slot: partial_relro_lazy_slot_write_redirects_call (a write of 55 followed by a call jumps to 55).
* It states that the calls work, not that the slots are protected; under the same placement the lazy slots stay writable (R3b, R3a).

**R4a** (`downDown_avoidsMut_of_firstPage_noMut`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Without the first-page condition the down-down mask can cover a mutable byte below the RELRO start: downDown_avoidsMut_cex_firstPage, and concretely endAligned_firstPage_mut_no_pageGranular_protection, where a program write to that byte faults. The statement "down-down never faults a legal write" is false in this toy without that condition.
* It does not say that down-down covers all RELRO bytes (for non-empty RELRO rs < re, coverage holds iff re % P = 0: R4b).
* For P = 0, floor division gives alignDown 0 a = 0, so the mask is empty and the conclusion holds trivially; this edge carries no information.
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**R4b** (`downDown_coversRelro_iff_end_aligned`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It is about the down-down mask alone; whether a real linker pads the RELRO end to a page boundary is not examined here (the GNU ld documentation of DATA_SEGMENT_RELRO_END and its common-page-size warning are quoted in the prior art).
* Down-down rounding of the start is covered by R4a (start-of-region condition).
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**R4c** (`downUp_coversRelro`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It does not say the down-up mask avoids mutable bytes (R4d).
* The empty-range guard in roundedMask is a modeling choice: without it, rounding an empty range [rs, rs) with rs % P ≠ 0 outwards would protect the whole page of rs. Whether any real loader receives or protects an empty RELRO range is not examined.
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**R4d** (`downUp_avoidsMut_iff_partialPages_noMut`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Covering of RELRO bytes by the down-up mask is R4c. Together with R4c, R4g and roundedMask_downUp_pageGranular, the auxiliary lemma downUp_covers_avoids_iff_exists_pageGranular shows: for P > 0 and RELRO bytes exactly a non-empty range [rs, re) (RelroIs L rs re, rs < re), the single interval roundedMask .downUp P rs re covers every RELRO byte and no mutable byte iff some page-granular mask does.
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**R4e** (`exists_pageGranular_covers_avoids_iff_noSharedPage`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Page-granular masks are arbitrary unions of whole pages, not necessarily one interval. The forward direction transfers to a single protected interval: if some page-granular interval rangeMask lo hi covers RELRO and avoids mutable bytes, then NoSharedPage P L holds, since such an interval is a page-granular mask. The backward direction does not transfer: noncontiguous_relro_noSharedPage_no_single_interval proves that [relro, mutable, relro] with P = 1 satisfies NoSharedPage while no interval [lo, hi) covers both RELRO bytes without the mutable byte. For contiguous non-empty RELRO (RelroIs L rs re, rs < re) and P > 0, the single interval roundedMask .downUp P rs re suffices whenever some page-granular mask does (downUp_covers_avoids_iff_exists_pageGranular).
* Bytes other than RELRO and mutable (code, .rodata) may be covered. The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* This is the separation of two sets by unions of equivalence classes, restated for pages; it is tiered T0.

**R4g** (`exists_pageGranular_covers_avoids_iff_partialPages_noMut`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The condition has two parts. "RELRO end aligned, or the shared last page holds no mutable data" is not sufficient: endAligned_firstPage_mut_no_pageGranular_protection has an aligned end and a clean last page, but a mutable byte on the first RELRO page, and no page-granular protection exists.
* Whether real linkers ever place mutable data on the first RELRO page below the RELRO start is not examined here; the prior art quotes documentation describing that hazard and a linker layout that places RELRO at the start of a writable segment.
* The proof composes R4e with the auxiliary interval lemma noSharedPage_iff_partialPages_noMut (same hypotheses).
* The toy tracks write permission alone (mapWr, stepProtect, AvoidsMut and ProtAvoidsMut concern writability and mutable bytes); execute permission is not modeled. A real protection call requesting read-only access (such as mprotect with PROT_READ) also withholds execute permission, so covering code bytes can fault instruction fetch even where the toy's avoidance condition holds; the card neither establishes nor refutes anything about execute permission.
* The toy has one page size P and unbounded Nat address arithmetic with no load bias. It does not model a link-time page size (common-page-size) smaller than the run-time page size, nor fixed-width wrap-around in a + P - 1 or in a load-biased address.

**R5a** (`applyAll_perm_of_addressOnly_of_nodup_slots`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* It does not assert the order in which any real loader applies relocations, including IFUNC/IRELATIVE relocations.
* Permissions are ignored here (applyAll); with permissions, order also matters if protect is interleaved (R1).
* Relocations whose value reads the slot's previous contents (implicit addends) are not address-only and are outside this result.
* This restates Bernstein-style read/write disjointness for relocations; it is tiered T0.

**R5c** (`applyAll_append_perm_of_resolvers_read_no_resolver_slot`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* The order family is the one produced by permuting within each group and applying A before R; orders that interleave the groups are not covered (resolver_reads_unrelocated_slot_order_dependent exhibits an interleaved order with a different image).
* It is a sufficient discipline; no necessity is claimed beyond the tightness witnesses listed in the hypothesis ledger.
* Each relocation is modeled as a pure total function of the symbol table and memory that writes one slot and ignores permissions (applyAll). Resolvers with side effects, resolvers that call other resolvers, faulting resolvers, implicit-addend and copy relocations, and dependencies between relocations of different objects are not modeled.
* It does not assert any real loader's ordering of IFUNC/IRELATIVE relocations; the prior art documents the within-table ordering of one loader version.

**R6a** (`runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Behaviour preservation is modeled as: every accessed section is kept. Address changes caused by removing sections, and code that depends on section sizes or on the absence of sections, are not modeled.
* The access kinds classify how the program obtains an address, so one run is encoded the same way under both policies; the policy enters through A3 alone. A1-A3 are sufficient, not necessary, for one given run: for example, under the precise policy a bounds access to an entry that an earlier edge access reached is kept although A3 fails for it (an example, not proved here). Over all runs they are exact: live_iff_exists_valid_run proves that a section is kept iff some run satisfying A1-A3 accesses it (the converse direction is exists_valid_run_of_live), so the theorem restates reachability-based GC soundness and is tiered T0.
* Edge and reference endpoints are not required to name existing sections: an index past the end of g.secs can be kept along a dangling edge (phantom_section_live).
* The GC graph models relocation edges, four section-level root flags (entry, exported, KEEP, retain) and start/stop references. Static-archive member selection (which happens before section GC), COMDAT groups, SHF_LINK_ORDER dependencies, special-section roots such as init arrays and notes, dummy (R_*_NONE) relocations, /DISCARD/ rules, weak references, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.

**R6b** (`keptItem_of_keptItem_of_coarsening`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Items stand for functions, objects or bytes; the kept byte set grows because each item's bytes are kept with it. Section-level attributes such as KEEP are modeled as root items.
* Coarsening can strictly enlarge the kept set, and refining an assignment can shrink it: secShared factors through secFine (coarsening_nonvacuity), and unreferenced_item_kept_when_sharing_live_section proves that an unreferenced, non-root item 2 is removed with one item per section (secFine) and kept when it shares a section with the referenced item 1 (secShared). So "GC removes every unreferenced function" is false in the toy.
* Even with one item per section, GC keeps root items and every item referenced by a kept item, including references from code that never runs (E records static references, not executed ones).
* KeptItem models item-level references and root items; section-name-dependent rules (KEEP patterns, __start_X/__stop_X retention, COMDAT groups, SHF_GNU_RETAIN on merged sections) are not modeled.
* This is the transfer of reachability along a graph homomorphism, restated for section assignments; it is tiered T0.

**R7a** (`precise_drops_unrooted_entries_of_noEdgeIntoName`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Modeling an undefined __start_X/__stop_X as a link failure is a toy choice; weak references and linker-script definitions of the bounds are not modeled.
* In the GNU ld and lld documentation quoted in the prior art, bounds synthesis and the conservative retention rule apply when the section name is representable as a C identifier, and a definition of __start_X or __stop_X in an object file or linker script prevents synthesis; neither condition is modeled.
* The second conjunct follows from the first: given that no entry is kept, a kept reference to the bounds is exactly StartStopUndefined. It records the toy's classification, not an additional fact about linkers.
* If no section is named X but a kept section references its bounds, RegistryKept holds vacuously and StartStopUndefined holds, under either policy (empty_registry_kept_and_undefined).
* With a relocation edge into one entry, the precise policy keeps that entry and removes the other while the bounds stay defined, so the registry shrinks without a link failure (registry_precise_silent_shrink); this is the witness behind the tightness of hN.
* The GC graph models relocation edges, four section-level root flags (entry, exported, KEEP, retain) and start/stop references. Static-archive member selection (which happens before section GC), COMDAT groups, SHF_LINK_ORDER dependencies, special-section roots such as init arrays and notes, dummy (R_*_NONE) relocations, /DISCARD/ rules, weak references, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.

**R7f** (`registryKept_iff_of_noEdgeIntoName`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Behaviour preservation for a program that iterates a registry is connected to runs by the bridge lemma runPreserved_registryScan_iff_registryKept: the run registryScan g i X, in which section i iterates the bounds of X and reaches every section named X, is preserved by GC iff RegistryKept g pol X.
* The pointwise form is the auxiliary lemma live_iff_root_or_conservative_reference_of_noEdgeIntoName (hypotheses hN and hj : g.nameOf j = some X, the latter tight by registry_iff_cex_other_name). Its two directions specialize to the auxiliary lemmas conservative_registryKept_of_live_reference (under the conservative policy a kept reference keeps every entry; hypotheses tight by conservative_cex_dead_referencer and conservative_cex_no_reference; instance conservative_registryKept_nonvacuity) and registryKept_of_entries_rooted (rooted entries are kept under either policy; hypothesis tight by rooted_cex_unrooted; instance registryKept_of_entries_rooted_nonvacuity).
* The hypothesis NoEdgeIntoName is tight over three-section toy inputs: without it, entries reached by relocation edges are kept under the precise policy although no entry is rooted (registryKept_iff_cex_edges_into_entries, registry_precise_silent_shrink).
* In the GNU ld and lld documentation quoted in the prior art, bounds synthesis and the conservative retention rule apply when the section name is representable as a C identifier, and a definition of __start_X or __stop_X in an object file or linker script prevents synthesis; neither condition is modeled.
* Marking entries as roots (KEEP or the retain flag) in the toy does not model static-archive member selection, COMDAT resolution, /DISCARD/ rules, compiler-stage elimination (R8b), or linkers and OSABIs that ignore SHF_GNU_RETAIN.

**R8a** (`survives_iff_compiledPath`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* survives_iff_linkReach: survival coincides with link-time reachability in the object the compiler produced, because that object's roots and edges lie on compiler-kept statics (compiled_of_linkReach). The conjunction form survives_iff_compileKept_and_linkReach_or_retain ((referenced at compile time or compiler-used) and (link-reachable or retained), for the record s with p.statics[i]? = some s) is therefore a definitional restatement: link reachability implies both its left conjunct and its right disjunction. Without the lookup binding the conjunction form is false (survives_conjunction_cex_without_lookup).
* Source-level reachability plus compiler retention does not imply survival (compileKept_and_srcReach_not_sufficient, card R8b): paths through statics the compiler drops do not count.
* The toy's compiler stage keeps a static iff it is referenced by compiler-kept code or compiler-used; compiler optimizations that remove referenced statics, LTO, and section merging are not modeled.
* Attribute designs differ across toolchains and layers, and the toy fixes none of them: its flags cref, cused, retain and lroot are independent. LLVM IR @llvm.used binds the compiler, assembler and linker (LangRef); C/C++ __attribute__((retain)) in GCC 11 and Clang is a separate attribute from used, and the Clang documentation states that it has no effect if the compiler does not emit the definition and that it is typically combined with used; whether unstable Rust #[used(linker)] implies #[used(compiler)] is listed as an unresolved question in rust-lang/rust issue 93798 (an open tracking issue, cited as background, not as normative).
* Prog2 places each static in its own input section (as with -fdata-sections). Without per-static sections a static can survive linker GC by sharing a kept section; the item-level model of R6b exhibits this (unreferenced_item_kept_when_sharing_live_section).
* Surviving both stages in Prog2 does not establish presence in a real final binary: static-archive member selection, COMDAT deduplication, /DISCARD/ rules, LTO, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.
* This is reachability in the subgraph induced by the compiler-kept statics, restated; it is tiered T0.

**R8b** (`compilerUsed_unretained_unreachable_removed`, `retained_but_compiler_dropped`, `compileKept_and_srcReach_not_sufficient`):

* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any real dynamic loader, linker or compiler.
* Instance (i) is the toy counterpart of the documented gap between compiler-level and linker-level retention (the GCC and Clang used entries, lld's start-stop-gc document, LangRef's @llvm.compiler.used, the Rust Reference's used attribute).
* Instance (ii) is the configuration that the Clang documentation describes for __attribute__((retain)) on a definition the compiler does not emit ("this attribute has no effect"); this is why the Clang and lld documentation combine retain with used. Attribute designs differ across toolchains and layers, and the toy fixes none of them: its flags cref, cused, retain and lroot are independent. LLVM IR @llvm.used binds the compiler, assembler and linker (LangRef); C/C++ __attribute__((retain)) in GCC 11 and Clang is a separate attribute from used, and the Clang documentation states that it has no effect if the compiler does not emit the definition and that it is typically combined with used; whether unstable Rust #[used(linker)] implies #[used(compiler)] is listed as an unresolved question in rust-lang/rust issue 93798 (an open tracking issue, cited as background, not as normative).
* Instance (iii) uses realistic flag combinations (an entry, a plain static, a compiler-used static); it shows that the second stage is reachability over compiler-kept statics (R8a), not source-level reachability.
* Prog2 places each static in its own input section (as with -fdata-sections). Without per-static sections a static can survive linker GC by sharing a kept section; the item-level model of R6b exhibits this (unreferenced_item_kept_when_sharing_live_section).
* Surviving both stages in Prog2 does not establish presence in a real final binary: static-archive member selection, COMDAT deduplication, /DISCARD/ rules, LTO, and linkers or OSABIs without SHF_GNU_RETAIN support are not modeled.
* These are single concrete toy instances; they show the corresponding informal claims are false as stated in the toy, not how often real programs are affected.

### Not examined

* Multiple objects and inter-object symbol resolution, `dlopen`, several `protect` calls, text relocations, copy relocations, TLS, concurrency, permission changes requested by the program, load bias and fixed-width address arithmetic (RELRO model).
* Section sizes and addresses, `/DISCARD/`, the C-identifier condition on start/stop names, weak references, linker-script definitions of the bounds, COMDAT groups, `SHF_LINK_ORDER`, static-archive member selection, LTO, and compiler optimizations beyond dropping unreferenced, unused statics (GC model).
* Whether any real linker places mutable data on the first RELRO page below the RELRO start, and which rounding any particular loader applies at revisions other than the pinned ones.
* Behaviour of any real loader, linker or compiler: only documentation and source text at the pinned revisions were read; no real tool was run.

### Escape hatches

The package has two impossibility results, R2a and R3a. Their plain claims are under Summary and Findings.

* **R2a** (`pic_rodata_slot_load_faults`). Proved escape hatches, each a concrete instance in which the other hypothesis holds and the load does not fault: after link-time resolution of the one-byte image `cfgSlotRo` (`linkResolve sa0 cfgSlotRo`), the `.rodata` slot is no longer written by a dynamic relocation (`pic_rodata_cex_link_resolved`; for every link-time and load-time table, see the positive control `linkResolved_rodata_loadOk_writeFaultsAfter_and_image`); and in `goodCfg` the dynamically relocated slot is a RELRO byte rather than a `.rodata` byte (`pic_rodata_cex_relro_slot`). A loader that makes read-only pages temporarily writable during relocation (text relocations) is not modeled; the result neither establishes nor refutes anything about such loaders.
* **R3a** (`lazyBound_not_callWorks_and_writeFaultsAfter`). Proved escape hatch: in the concrete instance `eagerCfg`, slot 0 is not lazily bound (it is eagerly bound, in RELRO), its call works and it has post-entry write protection (`eager_relro_callWorks_and_writeFaultsAfter`, which is also the positive control). Escape hatches that the toy does not model, and about which it neither establishes nor refutes anything, are listed in the card's fourth non-claim (a loader that changes permissions around each lazy binding, privilege separation for the resolver, non-caching lazy resolution).

### Unknown

* Hypothesis tightness: no hypothesis in any ledger has tightness `unknown` or `harmless`; every listed hypothesis is `tight`, with the counterexample named in its ledger row. R4e and R8a have no hypotheses beyond their universally quantified parameters, and R8b consists of three concrete counterexamples.

### Disproved or dropped statements

None. Every result listed in this report is proved as stated; no result statement was found false or left unproved.

## Evidence

### Kernel-check record

**Kernel check.** Observed on 2026-11-21 with `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only, no Mathlib. A fresh copy of `lean/` (without a `.lake` directory) was built with `lake build` with Lake's artifact cache disabled, so every proof was re-elaborated and checked by the kernel; the build reported no errors and no `sorry` warnings. Lean's `collectAxioms` was run on every one of the 762 declarations of the library `ToyRelroGc`: each depends on at most `propext`, `Classical.choice` and `Quot.sound` (298 declarations use `propext`, 101 use `Quot.sound`, 9 use `Classical.choice`, and 464 use none; per-declaration lists in `audit/axioms.json`). No Lean source of the package contains `sorry`, `admit`, `native_decide`, an `axiom` or `opaque` declaration, `implemented_by`, `@[extern]` or `unsafe`.

Basis for every result: execution (Lean kernel check). Every connection to a real system is a separate derived (modeling bridge) claim, marked where it occurs under Findings.

Results and their Lean theorems:

| Result | Kind | Tier | Depth | Lean theorems |
| :--- | :--- | :--- | :--- | :--- |
| R1 | theorem | T1 | shallow | `twoPhaseGuarantees_of_slotsWritable_of_protectAfterRelocs_of_covers_of_avoids` |
| R2a | impossibility | T1 | shallow | `pic_rodata_slot_load_faults` |
| R2d | characterization | T1 | shallow | `pic_loadOk_and_writeFaultsAfter_iff_relro` |
| R3a | impossibility | T1 | shallow | `lazyBound_not_callWorks_and_writeFaultsAfter` |
| R3b | characterization | T1 | shallow | `bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks` |
| R3c | theorem | T1 | shallow | `bindings_callWorks_of_eagerRelroOrLazyMut` |
| R4a | theorem | T1 | shallow | `downDown_avoidsMut_of_firstPage_noMut` |
| R4b | characterization | T1 | shallow | `downDown_coversRelro_iff_end_aligned` |
| R4c | theorem | T1 | shallow | `downUp_coversRelro` |
| R4d | characterization | T1 | shallow | `downUp_avoidsMut_iff_partialPages_noMut` |
| R4e | characterization | T0 | shallow | `exists_pageGranular_covers_avoids_iff_noSharedPage` |
| R4g | characterization | T1 | shallow | `exists_pageGranular_covers_avoids_iff_partialPages_noMut` |
| R5a | theorem | T0 | shallow | `applyAll_perm_of_addressOnly_of_nodup_slots` |
| R5c | theorem | T0 | shallow | `applyAll_append_perm_of_resolvers_read_no_resolver_slot` |
| R6a | theorem | T0 | shallow | `runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained` |
| R6b | theorem | T0 | shallow | `keptItem_of_keptItem_of_coarsening` |
| R7a | theorem | T1 | shallow | `precise_drops_unrooted_entries_of_noEdgeIntoName` |
| R7f | characterization | T1 | shallow | `registryKept_iff_of_noEdgeIntoName` |
| R8a | characterization | T0 | shallow | `survives_iff_compiledPath` |
| R8b | counterexample | T1 | definitional | `compilerUsed_unretained_unreachable_removed`, `retained_but_compiler_dropped`, `compileKept_and_srcReach_not_sufficient` |

### Statement and closure hashes

**What is hashed.** For every Lean name referenced in `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and the hypothesis `counterexample` fields; 298 names), `audit/statements.json` records `statement_sha256`, the SHA-256 of the UTF-8 text of Lean's `repr` of the declaration's type; `closure_sha256`, the SHA-256 of the sorted, newline-joined entries `name : repr(type)`, followed by ` := repr(value)` for constants that are not theorems, over every package-local constant reachable from that type through types, definition values and inductive constructors (theorem bodies are excluded); and `closure_size`, the number of such entries. For a definition, the statement is its type, so its body enters the closure of every statement that mentions it. The table lists these values with the axioms of each name (`none`: no axiom). Names are relative to the namespace `Toy.RelroGc`. Roles: `result` (a theorem of the result), `nonvacuity` (its non-vacuity witness), `control` (a positive control), `ce:h` (the counterexample for hypothesis `h`), `cited` (a definition, example, witness or auxiliary lemma the result mentions).

| Name | Roles | Axioms | statement_sha256 | closure_sha256 | closure size |
| :--- | :--- | :--- | :--- | :--- | ---: |
| `Acc` | R6a cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Acc.dst` | R6a cited | none | `8b8a21f170ef8a82f397cb0953dc94474c1fa3056bb471f1b80583dd5f9845c6` | `fb30db09a3bef5e3bcb639c2f203cdde265cd16377b34f558069bafa977324e7` | 4 |
| `access_predicate_examples` | R6a cited | `Quot.sound`, `propext` | `acfc8a480132b6719c03f7727885307454c8a9498fe1f4a51f9e51caacfc5f66` | `caca5d83262ae795e55731e072c7ff042527a8ccca06a6e5fa3446729dc79b84` | 31 |
| `addressOnly_examples` | R1 cited | `propext` | `8e49a2e397c046c3944cb24e2f4fe90976da79afb55f287c0c837f6e7d580309` | `4d75d9467672a8e2e39707c42a610d3f0b78723c82e16fd8690831fce5b78e7b` | 9 |
| `addressOnly_first_group_same_slot_order_dependent` | R5c ce:hNA | `Quot.sound`, `propext` | `0ba92f44d291ca162ba7c72e2d885f131194c8022121cda16602a145606b62aa` | `01d1864eb400dcf0ab09381fefb38054b4cc7c9317c41a47f608a2c9cc47f07d` | 14 |
| `addressOnly_same_slot_order_dependent` | R5a ce:hN | `propext` | `cdea66a7a671c01459f33087ac3f84d519bd146dab93c16774d814c9ea034e77` | `3a68ac54388cdfac987c0f2900b2f310abc5ad347fa860cf02aa1ed651571297` | 13 |
| `addressOnlyOrder_nonvacuity` | R5a cited; R5a nonvacuity | `propext` | `e37e551e7c99b20feec1c13fcd13d36b9181e58e6390d2dabb17dbb23c9da518` | `b247111566a5f70ff50360240e49a972b11d571a879a8f1888fc16c8f5324d04` | 10 |
| `align_examples` | R1 cited | none | `29cc6b8f75cd66a5b3ba525a2bb1802fdb61364b4e446ae44f515adddf05dd31` | `baab853ae7bbb03710b0c4c65f35d38893fa89cc4559cc9a8e9597417f2eee81` | 2 |
| `alignDown` | R4a cited; R4b cited; R4c cited; R4d cited; R4g cited | none | `aa7f57129bb56534d5547b81fc8edf5392d4891a73770ab420449675fc4f94b7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `alignUp` | R4c cited; R4d cited; R4g cited | none | `aa7f57129bb56534d5547b81fc8edf5392d4891a73770ab420449675fc4f94b7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `alignUp_eq_self_of_mod_eq_zero` | R4g cited | `Quot.sound`, `propext` | `e0d188775bbfdfe5f8471b2d3574678554924e451c9a9506ee2f6858ffaed497` | `0332a4ccc33a0f03ce631a14184463347b00584d7577e39c4b80a98e0100c156` | 1 |
| `applyAll` | R1 cited; R5a cited | none | `5417a596888500640c30cc03d4ae1aca7c49a0349a245179e4ee3c7129800faa` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `applyAll_append_perm_of_resolvers_read_no_resolver_slot` | R5c result | `Quot.sound`, `propext` | `7446a21ab95a7cf4f901fcb273109508154c6316fef48fa1741c223cc92038e6` | `83a5d07e0f5b962bf39e90d518b9d534eb529d90fe2bfcfad2170ddba89a501a` | 12 |
| `applyAll_perm_of_addressOnly_of_nodup_slots` | R5a result; R5c cited | `Quot.sound`, `propext` | `111354c1f0eb567629472a3b0a47eebbd4cc1a14659e8358db2b5d3704bad215` | `498f0a350ac649c654154cdfae0da6a36c2dd7107914486a1ec4a1798ee4f7a4` | 11 |
| `applyAll_perm_of_readsOnly_of_slots_outside` | R5a cited; R5c cited | `Quot.sound`, `propext` | `54aac58389fa2ff29f702ae0ce0145fa51b4b08e829f0861a4ea159e9d579704` | `595c0b0754da16ca8aa148afd0836c75199cd59790c3dd9a07c89b48f9511063` | 11 |
| `applyReloc` | R1 cited | none | `9fdb74d26c773032dddbd517f35b5d224d9e27c6221834f41b2a6296d2830136` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `applyReloc_comm` | R5a cited | `Quot.sound`, `propext` | `2de070d2bcc3a3b87069237c3b9612846a6b9c95ba53c576dba47ebe6411814f` | `ab56779a62bec23f1f737794e6e28105681ea45a46158ad6ac92abad7adc91d2` | 10 |
| `AvoidsMut` | R4a cited; R4d cited; R4e cited; R4g cited | `propext` | `dc26f8a9e33e3aaf6644c45d5bf2a8e5ed2ed340051da9cb8531a90375c7080f` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `binding_examples` | R1 cited | `Quot.sound`, `propext` | `0927cf03a79b0a90217a23e8360b2a5ff09ef6c6cc456c9bac3d740ed69e11d8` | `2976dc520eca1e244912e0782b88a4b233e7fc2468baa6d30ee4730eeda29fe8` | 73 |
| `bindings_callWorks_nonvacuity` | R3c nonvacuity | `Quot.sound`, `propext` | `ada923a8aa3fff498fe1c7c85fdb7139edadf2e036f4c5a57ea7130e3c5c5dad` | `91fdc5b9ca3337604989d073d1885d16e433d00cbc041a3e6778b2a11af72581` | 35 |
| `bindings_callWorks_of_eagerRelroOrLazyMut` | R3b cited; R3c result | `Quot.sound`, `propext` | `62ce60a303073fe0cd60af13a02e4a6d91b648755926921cc5a87909ce636263` | `963a0e0452e4385ddcabe0c33264e51aa08af4678c8767c98aede3831e2ea553` | 73 |
| `bindings_iff_cex_call_faults` | R3b ce:hCalls | `Classical.choice`, `Quot.sound`, `propext` | `683026839dd05b4b195d795e3efd87fe6b168c913262f88346295bf425242b1f` | `b943d9cc78208c8f34323fc98460f8494ba1011269bedf2cf8f40574466e7b31` | 76 |
| `bindings_iff_cex_eager_outside_relro` | R3b ce:hPl | `Quot.sound`, `propext` | `35ea1a581f622e0cd7ef2d4b44cdddac503d192bf4b0adce56f2f49bfda3359d` | `b0a3515bae9030f0481fdfd4bf70fecd6c133ff70c87c3c7e98375f41eeef0a4` | 75 |
| `bindings_iff_cex_no_cover` | R3b ce:hCover | `Quot.sound`, `propext` | `1a443bac773d14558759365e6d08963511060bb1196ed50d7552cd6d8cbb14d0` | `a943dcb13818bde5ff07a8512ca0841347ccb6da52f6434f5b5420c35c8a4cc8` | 76 |
| `bindings_nonvacuity` | R3b nonvacuity | `Quot.sound`, `propext` | `5bdfad9d1d556aa09dfb311c434511ebb3d692775623e189fc2a3639b8715484` | `e097f45cc3bc21432e26984f07cb2d816cae192360a52f3150b9bedd3a784d65` | 75 |
| `bindings_writeFaultsAfter_iff_eager_of_eagerRelroOrLazy_of_callWorks` | R3b result | `Quot.sound`, `propext` | `94dc0ef64b623b4eac04c3517c2a439489336be1450d59aa88f02644a414beb3` | `e031532400fe688a4123be8001865a9112a642d7643d22f234ebb929a7f91716` | 73 |
| `bindReloc` | R1 cited | none | `3e266ae898e17ab6a443e6db3c09b23d4f3b23b2be500619e3c39488c6852ef4` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `BoundsAccessesRetained` | R6a cited | `propext` | `6179da6d12fbe5a61bce9ac8b87a06a98b81b87a7602c3902ae8c3cae1c5c3eb` | `9da75f0f9d1634be9b5307e236c18bf15c87e3593d59a0c18d13a7d224eafd69` | 11 |
| `CallWorks` | R3a cited; R3b cited; R3c cited | `propext` | `2a32bd8252d09b997b79568e4616978fbd5f5d62ed4106951ea514825b72a4e6` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `callWorks_cex_cover_mut` | R3c ce:hAvoid | `Quot.sound`, `propext` | `5a5744133d27d4c989cb9211f1ff3628dec3b6b6d2349c8eeb7b976cfe6c224a` | `362e96ce654b7f619abed1023df5b45c3f792654a4bc471f3fc1aa1a119e08ba` | 76 |
| `callWorks_cex_lazy_in_relro` | R3c ce:hPl | `propext` | `b2e2514509387fe13f92adf776aebe3ca929ec989edce174da8347d7a9587112` | `9b507aaa2fddadf3c48018b8943651e464960fd95ebf6a75236e27ac2077b29f` | 76 |
| `callWorks_cex_slot_not_writable` | R3c ce:hWr | `propext` | `280919fd31ae642239d611424e5e923e9ccb7fa85993d8bf0308dd3bbdff3222` | `62eba978c2de5da67040d48354b01d074bbfbabe5af799848adb5deb660acadd` | 76 |
| `Cfg` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Cfg.start` | R1 cited | `propext` | `d19379f3b58d0208a185bf0d82a8c3c8666307563301d5576fabcf83ca7a9f31` | `43d836c6f85610e69207a4fbe1a89c51d300582d77ee889f4cdf7fd029cca98a` | 14 |
| `cfgMutCovered` | R2d cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `cfgMutReloc` | R2d cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `cfgNoProt` | R2d cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `cfgProtMut` | R1 cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `cfgRelroRo` | R1 cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `cfgRoMutReloc` | R1 cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `cfgSlotRo` | R2a cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `cfgTwoRelro` | R1 cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `coarsening_cex_not_kept` | R6b ce:h | `Quot.sound`, `propext` | `22bb8c5c2c9e5c838b0c643009e794b5bedebcec5094a120f115c26d0080e262` | `9e861734a8643f3ef6d2a4fad8e52cb962b988b8baa0dc4c4e43d9640e726e0f` | 9 |
| `coarsening_cex_refinement` | R6b ce:hc | `Quot.sound`, `propext` | `1413de5803d9a3260201b5c8c65eef0b0a3846b32d830294db5c2449ff23b670` | `5bdd9b940335e1bcd121fd3d17cae855e58d38e60c5a0d926518cfde2267f043` | 10 |
| `coarsening_nonvacuity` | R6b cited; R6b nonvacuity | `propext` | `2b4bc6a5eb0eafdd486f7182ad47101e8ccb472731adb7d6b920c80ed6fedd34` | `5bdd9b940335e1bcd121fd3d17cae855e58d38e60c5a0d926518cfde2267f043` | 10 |
| `compiled_of_linkReach` | R8a cited | `propext` | `06923129eef118628d6708dae90bb50a0aef7e04c2187bef18b8250318cc2670` | `0dbcf854709f4f19291be6b2d37cbf70ebe0aa1aa123ffc094dc464724566ae3` | 19 |
| `compiledPath_examples` | R8a cited | `propext` | `a10ba46aeff7c2028da0304bf20959692ac2e4d1a905de6dd7471c4fa99d99ba` | `358ff0c2246a1e85174c7b220f2e90a666b2af9a0cc0b9cd106ce60a7b529c04` | 18 |
| `compileKeeps` | R8a cited | none | `93187d5ffe2720851fc082d11ba207d28ad352034a922445a3285ad7a7407960` | `f5bb185b0467333d01f14914557e6bf2c068bba3841d2ac6915bfad8679586d3` | 2 |
| `compileKept_and_srcReach_not_sufficient` | R8b result | `propext` | `de7b1d00d02b9dc02a3da204da15568e03e22679ab2e7e3d5c4f3db433c9af70` | `2e73d7746143f3a82ff4878fafe19325c569f3cd0be923ad90cc6c21891dcf59` | 24 |
| `compilerUsed_unretained_unreachable_removed` | R8b result; R8b nonvacuity | `propext` | `d6397f0fa371a17928107f27aa8424e1ce67bc5cf1fc80dc27402b6d0e7b2790` | `f462c1396e6048895f386145dbb3f3ff8f1624771413137b0a94c0fa49a480e9` | 22 |
| `conservative_cex_dead_referencer` | R7f cited | `Quot.sound`, `propext` | `7f491e38f1f47356415a24dfaa1b5a06b307710d79cb791aee5e672fa93571f4` | `316a95cc9e9f8c2d2d0d117a5ef5dae801060b2e9fbc56084207ff896211830f` | 31 |
| `conservative_cex_no_reference` | R7f cited | `Quot.sound`, `propext` | `eb35928454d3119957b3804934db0ec87f677edaf7110c859373cc8bc0ae3104` | `b05491dec3efa5eaf5ab2ed189c92a2c991d801b0b4e8075ccf6de3f7a5df090` | 31 |
| `conservative_registryKept_nonvacuity` | R7f cited | `propext` | `298a2a3af4019d2e8acc917e59b13b8a1bf8708f4def26f050b9e16ef11be854` | `363b266fc16f2d6db8a74ce728586bca1079cee82e32e32796d1c642dac5e78a` | 30 |
| `conservative_registryKept_of_live_reference` | R7f cited | `Quot.sound`, `propext` | `bdcff18f2d373eff9e765a7fdcc6f803dfed428082d12dccd0def4be85812c26` | `dd84b1694f771bda657d6d982c1d23f103b2a1fb961516a62193257015ec197f` | 29 |
| `CoversRelro` | R4b cited; R4c cited; R4e cited; R4g cited | `propext` | `dc26f8a9e33e3aaf6644c45d5bf2a8e5ed2ed340051da9cb8531a90375c7080f` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `data_slot_cex_covered` | R2d cited | `propext` | `cc67f7e96ee3c58e3c5bb40e969c5c38ea741e3d8d8f76dce7d5aa38731317dc` | `2cf7d320d84f1fc68e8d527864f3a5ebca43cc676e68ba773cee1a66647ee9f9` | 71 |
| `data_slot_cex_load_fault` | R2d cited | `propext` | `b88daed93cf62243d24b41fe6fd3a17bf8633d732a0c5b63b8f2aa8d35716d04` | `6ac1b38bd21746da907a06173a7db65e4dcac4e849be988f23870b7368c948dc` | 71 |
| `data_slot_cex_relro_slot` | R2d cited | `propext` | `5e55f7bd43d2fc3a5867e28fb33b5a71e30f584b201b92ff7acf91d55a8787ed` | `e497f475525a7866101261c5b8bd31d25fddf9b4e8e70f0e12ec33200434c28b` | 71 |
| `downDown_avoidsMut_cex_firstPage` | R4a cited; R4a ce:hFirst | `propext` | `0c3540c73e159d43f1c72fb80862a319baeef5e55efc56b3e0dbc67380734e7f` | `f9cfe3d3712e3fad51fb53410cc804de43208e137c85349475078944a499e585` | 20 |
| `downDown_avoidsMut_cex_relroIs` | R4a ce:hR | `propext` | `ee809766cb5f35a62afd2711db7f104f74eaf5e39f88d314113c075cf61a725d` | `d5efe38ce3d4ace8631ed8c41e0001ab56593555db17696c1b34bedc149df014` | 19 |
| `downDown_avoidsMut_of_firstPage_noMut` | R4a result | `Classical.choice`, `Quot.sound`, `propext` | `cab6f11c0b6a9aa4e5b55040adba0ab29d17681673c4ec066980a755a8e9094d` | `d5efe38ce3d4ace8631ed8c41e0001ab56593555db17696c1b34bedc149df014` | 19 |
| `downDown_coversRelro_iff_cex_empty` | R4b ce:hne | `propext` | `79754d956d912a0a97b530bdc58abaec37696ce9196af16654b55daf5eb6fb5d` | `56590f668b3457fa7e42918f5042215f4237e4dfd8ece7c12ce38df928f49798` | 18 |
| `downDown_coversRelro_iff_cex_relroIs` | R4b ce:hR | `propext` | `b6da22282aaf00387ab21160eb0932e233e36564a8d50c47376f244392f0d1f8` | `ea8bb07329a80ab888133a81f434c3bf9e13d72ce848245272dafef3aaf59de4` | 19 |
| `downDown_coversRelro_iff_end_aligned` | R4b result | `Quot.sound`, `propext` | `19216dad5dbd02f075918d07dfb1f4227d3b3e24dfdb9355ad01cbba20755f9f` | `56590f668b3457fa7e42918f5042215f4237e4dfd8ece7c12ce38df928f49798` | 18 |
| `downDown_unpaddedEnd_tail_write_succeeds` | R4b cited | `propext` | `183beb59aa7119e4677f82f94b654f4a934a024dbf734c18e8da3cc9d0371b41` | `fa43f49932f805e7ac800b0c798724481f0f5f7511ea674231a91a067a00a1cb` | 80 |
| `downUp_avoidsMut_iff_cex_empty` | R4d ce:hne | `propext` | `4dcc582744ae2db14b49cb511132e812ecfb699c51e503a782743f2171e11e04` | `d5efe38ce3d4ace8631ed8c41e0001ab56593555db17696c1b34bedc149df014` | 19 |
| `downUp_avoidsMut_iff_cex_pageZero` | R4d ce:hP | `propext` | `bfe46dacea15bdecd49bae2fa55d4ae882200918330b98dbf6eafc404bd25dc9` | `f9cfe3d3712e3fad51fb53410cc804de43208e137c85349475078944a499e585` | 20 |
| `downUp_avoidsMut_iff_cex_relroIs` | R4d ce:hR | `propext` | `0f2c13f99e79f9edddaeb4e83874fdabd1de4b8a98080fe2f230e10573cc8452` | `d5efe38ce3d4ace8631ed8c41e0001ab56593555db17696c1b34bedc149df014` | 19 |
| `downUp_avoidsMut_iff_partialPages_noMut` | R4d result | `Classical.choice`, `Quot.sound`, `propext` | `ee97bbf9f3a49865db8dd3e0f0d3d6944961e53309146171d991bdfcd292024d` | `d5efe38ce3d4ace8631ed8c41e0001ab56593555db17696c1b34bedc149df014` | 19 |
| `downUp_covers_avoids_iff_exists_pageGranular` | R4d cited; R4e cited | `Classical.choice`, `Quot.sound`, `propext` | `f0f270b16793a33d68cb8ae973eb939e80b745911a0b4640769bf8ee251c558b` | `69dfd9945c7fc0ef5eb8d264828e7c50c5c5ad91b895e2af305a3528bde4b66e` | 20 |
| `downUp_coversRelro` | R4c result | `Quot.sound`, `propext` | `8ad9005cfdc446616457f8faedbd0f125fb3333d873f373e220aa14286e8bf85` | `56590f668b3457fa7e42918f5042215f4237e4dfd8ece7c12ce38df928f49798` | 18 |
| `downUp_coversRelro_cex_pageZero` | R4c ce:hP | `propext` | `71b0b7c001f991c78ce69920b0423f2d43840554115242ce425af99fe1723cbc` | `ea8bb07329a80ab888133a81f434c3bf9e13d72ce848245272dafef3aaf59de4` | 19 |
| `downUp_coversRelro_cex_relroIs` | R4c ce:hR | `propext` | `81d4bf8cfaf91c2137f7bf1621b65f4c69622849304c655545706c408d7f9986` | `56590f668b3457fa7e42918f5042215f4237e4dfd8ece7c12ce38df928f49798` | 18 |
| `downUp_sharedLastPage_mut_write_faults` | R4d cited | `propext` | `6c3d6a7db24f71c5112520eeb996170d5d8baa9364a8218f82b0ded12480cdd4` | `11a1d434f869061ab88d8d84f79b5175a3fafbbac0cb65b86bcafc8af39b7d41` | 81 |
| `eager_relro_callWorks_and_writeFaultsAfter` | R3a cited; R3a control; R3a ce:h | `Quot.sound`, `propext` | `234518b3758baf77f011cb55ba03730d3002079bd131b7768c3f4413ec81ed79` | `5c8f624e9cb3329c5fa78dec0fc302432ac8f23d3875399461fbff7a8be5aead` | 73 |
| `EagerBound` | R3a cited; R3b cited | none | `1713edba870a5c7e99db5c567ab399f8d1f7a8e93748432082c17dac5690eaa8` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `eagerCfg` | R3a cited; R3b cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `eagerMutCfg` | R3b cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `EagerRelroOrLazy` | R3b cited | `propext` | `f3a08163b00e3b861ba20a9bbd342da1359adfda9cb302c02ab08583ac88c5a1` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `eagerRelroOrLazy_examples` | R1 cited | `Classical.choice`, `Quot.sound`, `propext` | `dc28eb44bd3199fbf546ec87c6dd6ead930b0bb0450d63c20381fd85d7c84a96` | `6ea36fa9712e5f738a22d6291b45c5afd5c4ccba6d85154735f487eaafe11920` | 26 |
| `eagerRelroOrLazy_of_eagerRelroOrLazyMut` | R3b cited | `propext` | `8ded98375e27ae4c4146c98922167223dbe00864c117e51a92bbeca588747faf` | `e9765bbce02dbf87937b16cd0d0035237e420a7d659f07fbec96c98fe9cc1320` | 23 |
| `EagerRelroOrLazyMut` | R3c cited | `propext` | `f3a08163b00e3b861ba20a9bbd342da1359adfda9cb302c02ab08583ac88c5a1` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `eagerRelroOrLazyMut_examples` | R1 cited | `Quot.sound`, `propext` | `47ac744f0cb1b31684876fd81243e22d78ba986334c2c131bbf605f20c5b833f` | `0318f47063d6870a1e1542d742d2cb9d0df30937466147512cbd0a71597aedff` | 25 |
| `EdgeAccessesFollowEdges` | R6a cited | `propext` | `99336562adf45927f4c17261b742d17075ba878ca87f7c5e6221cb76c6f2db39` | `fb30db09a3bef5e3bcb639c2f203cdde265cd16377b34f558069bafa977324e7` | 4 |
| `empty_registry_kept_and_undefined` | R7a cited | `propext` | `44055bcc3105123a0482ee0d68f3d45b7255ef1e7e518858b6c7e0546d62ecc2` | `2d8f5984322e9c165eb5928a0d0c005f82eb56e242d478abd3c348b726e08c9b` | 32 |
| `endAligned_firstPage_mut_no_pageGranular_protection` | R4a cited; R4g cited | `propext` | `7ba1e187d46ef34238aea41875d9f6e265089626c24308e8ac45b51397b20a35` | `a2a16e170641d6bb4f60b29db40cbeb5222362e06ef06bfa86e099e92bd86c2e` | 83 |
| `Ev` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `exists_pageGranular_covers_avoids_iff_noSharedPage` | R4e result; R4g cited | `Quot.sound`, `propext` | `438755f314fe09156a29daa0b547c2438c3db5270d861050dac3a2bd705313c5` | `72655c88127b57568069c7e5f1af5d5f1b39f02257b7efa5b28b1aaef4cb563f` | 9 |
| `exists_pageGranular_covers_avoids_iff_partialPages_noMut` | R4g result | `Classical.choice`, `Quot.sound`, `propext` | `e3b2b645e17c0eff4622348861fe06a27560f3228e6f1488ccb80c87962b914e` | `06e446c851f73c6aa70b4dec3d4240e5fec6db167dec74c701fbabeaa14cf810` | 12 |
| `exists_pageGranular_iff_cex_empty` | R4g ce:hne | `Quot.sound`, `propext` | `15b8bb96fd6041d7da75cf5b69ed994519f2fc305ea27e36a7c5b7d1ce71ce9f` | `06e446c851f73c6aa70b4dec3d4240e5fec6db167dec74c701fbabeaa14cf810` | 12 |
| `exists_pageGranular_iff_cex_pageZero` | R4g ce:hP | `Quot.sound`, `propext` | `bec08441633b9b49826c0cd284ad02cd88aba196f2bac65fbb6de31b453ac360` | `06e446c851f73c6aa70b4dec3d4240e5fec6db167dec74c701fbabeaa14cf810` | 12 |
| `exists_pageGranular_iff_cex_relroIs` | R4g ce:hR | `Quot.sound`, `propext` | `0e2484b39ec1d779435bd082e78bb752223291d92aff0a964ebb3c667756f0d4` | `4df583ef9270e366968fa28c704eadb2dd98da36bbaec332ecc02aad5e8f03df` | 13 |
| `exists_valid_run_of_live` | R6a cited | `Quot.sound`, `propext` | `94927b03875446d96eadaebc6d9aed74f21236f2b9530fabe764745d8ea00867` | `618f30a5387be060cf66c0af12a0a9006cc15302420949ba91e2550cd34b4f3a` | 40 |
| `gcDeadRef` | R6a cited | none | `a6b6987029ee46374c84f061368b007bd40ec98001e5ce6f7f89151c65548c26` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `gcEmptyReg` | R7a cited | none | `a6b6987029ee46374c84f061368b007bd40ec98001e5ce6f7f89151c65548c26` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `GcIn` | R6a cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `GcIn.IsRoot` | R7a cited | `propext` | `95a33231496bdcb67426d8db24de62db4f27784c0c56c466fcd30d810905ebe0` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `GcIn.isRootB` | R6a cited | `propext` | `be894379b8c7ddb90fd80d20890a108d615348c1c68cd92b9d3455ad0076f90a` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `GcIn.Live` | R6a cited | `propext` | `6d6f8154e1ac134794470851f325f0e4ce288e309baebc1871f495357b4590a6` | `e5ad74fa4572e1e41ad967dd5c474b67f6fcbc85ca22618734d8e4fc2af68ed4` | 7 |
| `GcIn.nameOf` | R7a cited | `propext` | `ceec63494e54ca11b95a32d8a5fdfcb686518c4a5d2fc74439023114337e803b` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `GcIn.ssEdges` | R6a cited | `propext` | `b660613809e09213d82da6766d035e0e35cf45d7a5d7a59a75e89492479455f3` | `e5ad74fa4572e1e41ad967dd5c474b67f6fcbc85ca22618734d8e4fc2af68ed4` | 7 |
| `gcPair` | R6a cited | none | `0c5eddbe58c5410826e6a6c925c17524b63141782ff8c35a8b8be46f3152a8a8` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `gcPhantom` | R6a cited | none | `a6b6987029ee46374c84f061368b007bd40ec98001e5ce6f7f89151c65548c26` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `gcReg` | R6a cited; R7a cited; R7f cited | none | `d6ae3d7f21a021256ad5cf8312cf67c3007d88d6688edbf06a3eb46584951296` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `gcSoundness_bounds_nonvacuity` | R6a nonvacuity | `propext` | `aa7e7cba9a9ba45e6d1ea957e6cbc0fe07a78347bf0eb76a20491127e10ce858` | `cd7ffc5277a82e086421420eb0c1f560dc0b45352f9f36952d3df26a7193d098` | 34 |
| `gcSoundness_cex_bounds_access_unretained` | R6a ce:h3 | `Quot.sound`, `propext` | `bd0eb58c0b7c60968232386b7bbfc7779a226c5f98b1b738e437f3b77d5170b6` | `1b03070e24757fcf0de23d52c36ca40ae7c13b5b2c5c1fa8fe8fd241671dfa3a` | 43 |
| `gcSoundness_cex_edge_access_without_edge` | R6a ce:h1 | `Quot.sound`, `propext` | `b1e74d6050c2e43713d95bc0c235b1f4c1ad36c3cb485e4e5a67993a91b2214d` | `acd01f098a6d8aa16f662bcd7fc87ec322cb61d2ed4070a557a1bd3a4eacf0f1` | 42 |
| `gcSoundness_cex_implicit_access_to_nonroot` | R6a ce:h2 | `Quot.sound`, `propext` | `1399ec55d6073c530b432b1817f69890048dc90750b07d857bde94f3d8f8a66b` | `acd01f098a6d8aa16f662bcd7fc87ec322cb61d2ed4070a557a1bd3a4eacf0f1` | 42 |
| `gcSoundness_nonvacuity` | R6a nonvacuity | `propext` | `b527451001bb3f607bcf928fbacc7450c135a074a0e80950a377f51573190df7` | `33522fb4fc9c7314c4b9b4c4662373706a331669f0bc47c347773061448443a0` | 33 |
| `goodCfg` | R1 cited; R2d cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `ImplicitAccessesHitRoots` | R6a cited | `propext` | `1040acf5c9c1e2b09a64affad329e2ef26e212f63ea59396d26444f24fe7e11b` | `fb30db09a3bef5e3bcb639c2f203cdde265cd16377b34f558069bafa977324e7` | 4 |
| `insertAt` | R1 cited | none | `21fc51a2b7c0680b1112acf08190399557ac1c422cb2657d535a49d09e9d289c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `itemEdges` | R6b cited | none | `36379671fe9f33b65fe131fbe91a267ba5889fc24e4524c1e62fde4c39a3261b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `itemRoot` | R6b cited | none | `4d0bb073ea64b29daa58ca1e1a5651489320de5e9f68f4613d552b0719c0b935` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `KeptItem` | R6b cited | none | `13a0d2a3f155229e2bb4ebbb93394a1d4d31b7f4495528174fb71a50a00377c3` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `keptItem_examples` | R6a cited | `Quot.sound`, `propext` | `6d7ccc7f83315f8330658fd4ba141c4eacef259db60d94b819edb632a10a33e2` | `9e861734a8643f3ef6d2a4fad8e52cb962b988b8baa0dc4c4e43d9640e726e0f` | 9 |
| `keptItem_of_keptItem_of_coarsening` | R6b result | `Quot.sound`, `propext` | `a57ba05893d4952d61e1d31f9a5dabe92d61841d5d54b48275ece85197c24901` | `2d1c8b5d0cdd1812c3dddb8873439dcbbf7543f45e2706f9e1ebda1ebd120024` | 6 |
| `Kind` | R4e cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `layoutMutRelro` | R4a cited; R4g cited | none | `b3359fa06019a8117c424f174ee8603e4146a87e6a3694f4f9c2dc93dd194c54` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `layoutRelro3` | R4b cited | none | `b3359fa06019a8117c424f174ee8603e4146a87e6a3694f4f9c2dc93dd194c54` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `layoutRelro3Mut` | R4d cited; R4e cited | none | `b3359fa06019a8117c424f174ee8603e4146a87e6a3694f4f9c2dc93dd194c54` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `lazy_inside_protect_writeFaultsAfter_first_call_faults` | R3a cited; R3a nonvacuity | `Quot.sound`, `propext` | `9f698483ac4c4b4452fdba9e019ea025592ee6b012dfe09b0eb3458567eff007` | `8716b41463991e2b8a964296081a7ed1b4d6c85b920cb60b8397eb2d7577b9ad` | 69 |
| `LazyBound` | R3a cited; R3b cited | none | `1713edba870a5c7e99db5c567ab399f8d1f7a8e93748432082c17dac5690eaa8` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `lazyBound_not_callWorks_and_writeFaultsAfter` | R3a result; R3b cited | `Quot.sound`, `propext` | `d9dae162507e4cfb1c047967fa689bca825837ebce31ec955f04f4440a8bc087` | `fc25c81494e289ba74ee2c0dff59777e33e331380bb9f43894776eb8319f2f56` | 68 |
| `lazyMutCfg` | R3a cited; R3c cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `lazyRelroCfg` | R3a cited; R3b cited; R3c cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `le_alignUp` | R4c cited | `Quot.sound`, `propext` | `604af58a39b62c3bf8ebfad900c12b5077300b9197457302901f992c3f4fdefc` | `0332a4ccc33a0f03ce631a14184463347b00584d7577e39c4b80a98e0100c156` | 1 |
| `linkReach_closed` | R8b cited | `propext` | `9d6aea3b4d1fce2a2078178e40709b507fe7e01e421a87f51a472ac69274e983` | `76f41b71c7678f71511df253b957c2bddc7f773930aa69aeaf96538d1fb05e3f` | 21 |
| `linkResolve` | R2a cited | none | `21ac3ad303ce38297f679c18e3e8b6fc1728592aa552472427d54f86e32bf9b6` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `linkResolve_examples` | R1 cited | none | `0d1bc191116cae0791fce3034b8cfec3f0e9e58e136e2317955c0c6a9164fedd` | `e33d02be4c0033a43f7e7bb1504c5559c8da3c17ce4d4a4ee9e50ed6565070ff` | 28 |
| `linkResolved_rodata_loadOk_writeFaultsAfter_and_image` | R2a cited; R2a control | `Quot.sound`, `propext` | `d579920bb54f0e42448871ba34b4755dc2cc5f5d09fb6ce99f0e9fbc6ebf07c8` | `8a63519e5ac0fc234bdb502afa985ce236d6d880391f13a0532335455d702558` | 68 |
| `live_examples` | R1 cited | `Quot.sound`, `propext` | `55ddbd8af3b74acf934ed95604434818da10fed406fff1b435c0f520d96ea572` | `2b7d2f6c54bf60f900c1c46ca6d376100af0ced491afb6e833e77b72f6f248a4` | 29 |
| `live_iff_exists_valid_run` | R6a cited | `Quot.sound`, `propext` | `c995c2df30d0c2a92c3386b006eb7b5441badc9f424ef308a865a372f0c44595` | `618f30a5387be060cf66c0af12a0a9006cc15302420949ba91e2550cd34b4f3a` | 40 |
| `live_iff_root_or_conservative_reference_of_noEdgeIntoName` | R7f cited | `Quot.sound`, `propext` | `ddb0d1209e71b14937da2b9fbf59a3fc4398efec566175316524c5f121276757` | `4f6081ddba9f53182d4fe332b8ae54890730156db04b607357c8dc45846e7d99` | 29 |
| `loader_predicate_examples` | R1 cited | `propext` | `874f1cc2b292347914d388a0fb597f56a261254204e00b418cde1e3021dff4df` | `a9b0a19735c0d40420c5b1fccf11199fbde9e9cc50543bd88ea58e593a533499` | 77 |
| `LoadOk` | R1 cited | none | `85ffe4213f8813157cb998a051b8755f40ca878cb2c120ae5a1370e94f2b1353` | `fb84a5f312f458d85f2699e914d491dfda7e0ee76c0d5154b7b42ae1945cd2d4` | 7 |
| `loadOk_twoPhase_iff` | R2a cited; R2d cited | `Quot.sound`, `propext` | `5c8b723b6d65b0c71aefac6f4dc0072842bab2fef526068e1deee4bddb02520f` | `a331b49f7119d1de5b8180de320358528ac2080a367dde21057b156419a74778` | 66 |
| `mapWr` | R2a cited; R2d cited | `propext` | `295dda619825535c39a08f4d779be4877b82f6152d1ad1a7f9bb8be2ea6665c8` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `mapWr_examples` | R1 cited | `propext` | `11388bea0055e6ca2edd68912023caad013f68826d7840ac8283acb5e387f1fd` | `7dd3935d432deebf701b717083abdb5e6b6e7f850d29877d42ca27b2a3b31230` | 12 |
| `Mem` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `mem_ssEdges_conservative` | R7f cited | `Quot.sound`, `propext` | `ea1625bb44e9eb9174250737225b52a9529b48394bed11bb05d5762d17c09ee2` | `7c3c2308e8cdc8909cb51ab426bae1cc05cefc63636e0ee968caaca019f29b88` | 15 |
| `mixedCfg` | R3b cited; R3c cited | none | `3ce58ade0eb859cfffe0145531b48f3c640f5dc38a91324929533bff5aef8192` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `mkSec` | R7f cited | none | `57a80656f153f8e67a009380cb45003a6252384d1644f8dc228ba6a95ecf8a91` | `706b28667cb4d8d67efba8614f296810f4bbd0eceafa6a741c409d4443bfbf72` | 2 |
| `NoEdgeIntoName` | R7a cited; R7f cited | `propext` | `db5789f3ef1fa1284bed1512c00728720e43188b06e798b9e182fb705e8dc1f4` | `4be2507279dbd8274753c38761475a3dfec7c79fca20613cf10e57a50d82743e` | 4 |
| `NoMutIn` | R4a cited; R4d cited; R4g cited | `propext` | `02c57c4d567ae93df5b52ee3080904b2197d4c973c41691487bcaa097d78d795` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `noMutIn_examples` | R1 cited | `propext` | `3dd0694eb5886e02da4f630ee3fa655456212aae72390d17a73064c491cba640` | `195cdfe2d1ffd39dde7500b3e8fd87993bc76af5c9c94841f15a05d7f4d452c6` | 7 |
| `nonAddressOnly_first_group_order_dependent` | R5c ce:hA | `Quot.sound`, `propext` | `22c4bc37176afce1114d2856b313a9df213e2d6bfbc742493f901caff41c9884` | `b2dff82e617962cdfe1df627cd00398b50c7a8167d5114cade78a7d7a981e74e` | 16 |
| `noncontiguous_relro_noSharedPage_no_single_interval` | R4e cited | `Classical.choice`, `Quot.sound`, `propext` | `a179a4311c1c88b0a1c0f099be505b3bb22429e61c6a91a75c7f3fa51c0ee143` | `9bc5e0e57c53ca60ef13fcf9e587eddde8abbfbc774f22fc0222aac1f2f2d58c` | 9 |
| `NoSharedPage` | R4e cited | `propext` | `a6b23485f136b01036164f76afc950f0a54b8a591298c6b32b2285686af6ec23` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `noSharedPage_examples` | R4e cited; R4e nonvacuity | `propext` | `7c99cea5d94e8d7ecb3e6292cc59e5a375388e3dc409cd6456aae61e0659acf3` | `8059dcab3477e7fdf973f997717520f5acbcfb79c6c02abc399400497dc24932` | 7 |
| `noSharedPage_iff_cex_empty` | R4g cited | `propext` | `c2d6faea023a5a3a16b1028dd752a59c49864d8ff12221758601b80ace68561b` | `7f8cba5f061a0649a14625213c9f747cdc5fb23986e1f17f5dd9ce229b9e8f50` | 10 |
| `noSharedPage_iff_cex_pageZero` | R4g cited | `propext` | `78bed6259dfb6bfde7d9e4652d2026aaf93c61544e5980b4ec0074d2f36a0784` | `7f8cba5f061a0649a14625213c9f747cdc5fb23986e1f17f5dd9ce229b9e8f50` | 10 |
| `noSharedPage_iff_cex_relroIs` | R4g cited | `propext` | `f37e54e8f9147cd8e7e425dc55eb407c7fc9bed755a6ad6b5152fc5afb58dade` | `9ef2869077e7286f309150b812590c9edfc2988f65640cc2398b4436d5d150c3` | 11 |
| `noSharedPage_iff_partialPages_noMut` | R4g cited | `Classical.choice`, `Quot.sound`, `propext` | `b895f01d79dcce61fa8f4104cf923688e40a2e90db31c4a03033406c2b4633cb` | `7f8cba5f061a0649a14625213c9f747cdc5fb23986e1f17f5dd9ce229b9e8f50` | 10 |
| `Op` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `order_cex_not_perm` | R5a ce:p | `propext` | `6910423a90e07257410ae49d5b2c407e6ad66d143e0ea2745cfb20f1c79df95e` | `3a68ac54388cdfac987c0f2900b2f310abc5ad347fa860cf02aa1ed651571297` | 13 |
| `Out` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `PageGranular` | R4e cited; R4g cited | none | `2e33e7730e712664cedd5a618bd13a45372089e4dab3c62b2a37ae598a6e8f9c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `pageGranular_examples` | R1 cited | `Classical.choice`, `Quot.sound`, `propext` | `983a5f5bbf890db06b9605060745c7b7ddabdaa96f278ec1f8002ac8469f7446` | `a277a2dccff1a0f62fb0706f54e844a3ea4a7f261262363fb065c11ed46c6687` | 2 |
| `pageRounding_nonvacuity` | R4a cited; R4a nonvacuity; R4b cited; R4b nonvacuity; R4c cited; R4c nonvacuity; R4d cited; R4d nonvacuity; R4g cited; R4g nonvacuity | `propext` | `d43226fdcde023d6438af4dd1faa96ee02fd453cebee15c2ba248563a98ffdca` | `785f78509530df77e7bee587da1195a3b6a1d712c7aa16be1f3290c1933da3f9` | 20 |
| `partial_relro_lazy_slot_write_redirects_call` | R3a cited; R3c cited | `Quot.sound`, `propext` | `1ee801fbbe78a032abc9e833d3d7d1db65adb890f6f43cf211077a259ceccee2` | `e1e239dbbc021ec4d6ddc8593b6c5c74f0a837ca2cfbab40bc849239384ca5bf` | 69 |
| `phantom_section_live` | R6a cited; R7a cited | `Quot.sound`, `propext` | `83fa5d73d1b7cfbf3d2ef7e4c0af841be176f4e3fa2f6539882b32c278c642ff` | `3412e098a1b06e82054d3b9353d204cc13daa73625feb02b804f84897b97c160` | 31 |
| `pic_data_slot_loads_and_write_succeeds` | R2d cited | `Quot.sound`, `propext` | `c2ce8741f21fee75a0abb43239d5dc20476e9b34de20d573104584e5e08fa98f` | `396ace43281b9c1375df54b1f52eef176179e1ebc7cf00ebac08567d6861f76d` | 68 |
| `pic_loadOk_and_writeFaultsAfter_iff_relro` | R2d result | `Quot.sound`, `propext` | `bfaf7d35e884d3cbea6a891df16005569536d41e72081a4decb85b58acc02cb4` | `babaeb635743872f90a810fac964873f41ad30c659c9eed2e7e7362be7041b2f` | 70 |
| `pic_relro_slot_loads_and_writeFaultsAfter` | R2d cited | `Quot.sound`, `propext` | `c4ef3f9ea09146dd8c6cf75292662f76d4f02a34641f040de1bdd1ace8049856` | `f692320951614f19a72e2c64bcb4740d715bcd0ac499fd61fabf3b25b8c5053f` | 69 |
| `pic_rodata_cex_link_resolved` | R2a cited; R2a ce:hr | `propext` | `c1344bef6be3fe9bfb831aaf73a27eb3918614249a45e7da83243c25169cf244` | `b90b99ac4382695f4db2f7fbd447b4536d2069ad9d7d99313656ac64aab9df2a` | 72 |
| `pic_rodata_cex_relro_slot` | R2a ce:hk | `propext` | `c976884acf83c370bf76b160684ad1b7a997b94b055bef067d2d182b224b20c9` | `a60a99e97e91a2bf258d57d4cd069a8f3a55c8a73cd333d966ee7ea7fe86a7fc` | 69 |
| `pic_rodata_slot_load_faults` | R2a result | `Quot.sound`, `propext` | `dac426ec42f670b9d6aac1dcc5b2c44e080568d065732c8ac09927cbc5feef44` | `76e0cde90f7bde5f4143416ddac6a415a4ba7feb2cef3bd49164937a366b18d6` | 65 |
| `placement_iff_cex_cover_mut` | R2d ce:hAvoid | `Quot.sound`, `propext` | `e984a0ca58c9951401a4518e4760baf3d58cec9ee44ea223a727c4cd70fa0206` | `4a665af55e230301c026e345c285702b3d913875784a2857837855612c5ad3af` | 74 |
| `placement_iff_cex_no_cover` | R2d ce:hCover | `Quot.sound`, `propext` | `074158b29196db63db2b197c510bf34ed07905e8af69a1120129130c9ed06e7c` | `6a93299149030bd7fc0e44de4381a8db78509666b13285351ac0b550a39c1834` | 75 |
| `placement_iff_cex_not_dynamic` | R2d ce:hr | `Quot.sound`, `propext` | `47e6b723807f6058b42a6f8db5dd213200df0fea4c17142676eda9a0283197ec` | `a2d3e543a239cd24d6e57d39a5feb9943ca340fd72549cc357685d62957f5e36` | 77 |
| `placement_iff_cex_other_reloc` | R2d ce:hOthers | `propext` | `2c25914a4c2886aac0eeb9be70704ccba9deff134830d7386647a8c0352a3589` | `ebff70e73fc03f07639cc3fef7ccf6ed8c19af90320f5b37c95ca3f792d9c828` | 73 |
| `placement_nonvacuity` | R2a nonvacuity; R2d nonvacuity | `propext` | `117b67bbe19ca3beff127ee136974defd6afb4b348940168e3fcca8fcd110a1e` | `2c9050887e45325895f26f3b0a1c1b15e733524c6b3d5e1de69fc7ec0823c9cb` | 36 |
| `postLoad` | R1 cited | `propext` | `89b6926d22e8b1705407e8e642e4cee322dce59629d106c8e7d7d27fd82395f0` | `43d836c6f85610e69207a4fbe1a89c51d300582d77ee889f4cdf7fd029cca98a` | 14 |
| `precise_drops_cex_edge_into_entry` | R7a ce:hN | `Quot.sound`, `propext` | `437d90681d4e1aa3bde3ad7b970dd92af47c9e476be8e8b30c6dcb7f5090d67c` | `73418e1c677f3115f7d9dc967551216ab15de18b247f97335504232fba3c0dff` | 31 |
| `precise_drops_cex_rooted_entry` | R7a ce:hU | `propext` | `86673bfd3765f82791414567d930a48d132a8d94dda4e99596dc0752a746e16c` | `73418e1c677f3115f7d9dc967551216ab15de18b247f97335504232fba3c0dff` | 31 |
| `precise_drops_unrooted_entries_of_noEdgeIntoName` | R7a result | `propext` | `dd5a5c63bc3cd72219ef2b1f3a8a0a69dc8b953955cb838570f0f025c02f770a` | `f44f6bcc97a01162a9fc45675dee21b22c9db514a17844f418769dfd94a09735` | 30 |
| `Prog2` | R8a cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Prog2.compiled` | R8a cited | `propext` | `24956396b4da94d0353e4e11bf940c89a105499b20499ecee4c7782ede1907be` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `Prog2.CompiledPath` | R8a cited | `propext` | `8f003a145607ecedbe5bba73b9c65d99e3f44e36ab8400a10105b320d7783405` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `Prog2.LinkReach` | R8a cited | `propext` | `5997c3ca018834875d3d40d8a62f63e87386ba63f02d22fbfbd5bba38abb08f7` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `Prog2.objEdges` | R8a cited | `propext` | `cc274bc1458c0724a6ff8a4c7f41a96aa1390059240c0c9a8f2d3d7107788c7c` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `Prog2.objRoot` | R8a cited | `propext` | `5997c3ca018834875d3d40d8a62f63e87386ba63f02d22fbfbd5bba38abb08f7` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `Prog2.objRootB` | R8b cited | `propext` | `24956396b4da94d0353e4e11bf940c89a105499b20499ecee4c7782ede1907be` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `Prog2.SrcReach` | R8b cited | `propext` | `5997c3ca018834875d3d40d8a62f63e87386ba63f02d22fbfbd5bba38abb08f7` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `Prog2.Survives` | R8a cited | `propext` | `5997c3ca018834875d3d40d8a62f63e87386ba63f02d22fbfbd5bba38abb08f7` | `aada7b33d5ed4f283a423b5bc8b38de064e4a3f1bff5bbff0b9de0854c745a8d` | 4 |
| `ProtAvoidsMut` | R1 cited; R2d cited; R3c cited | `propext` | `7960ad8d7d2d8810f18fea41765c15f95bd8f3769e875639c9d7faa5982fbb3e` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `protCfg` | R4e cited | none | `7a356fb184095fb7b7d9c102f092c82e4ce4d64571520b31a5ff55ceced73760` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `ProtCoversRelro` | R1 cited; R2d cited; R3b cited | `propext` | `7960ad8d7d2d8810f18fea41765c15f95bd8f3769e875639c9d7faa5982fbb3e` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `rAddr0` | R5a cited; R5c cited | none | `a2b9b39c81ddb775335091517229b06263028a9d38fcbbfc7f9617a8ec723ad7` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `rangeMask` | R4a cited; R4e cited | none | `60ef229f7f6cbcf5de1effb81f541c6e4f0953822ee4ba59fcc23ad08c4fa3d8` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `rConst0` | R5c cited | none | `a2b9b39c81ddb775335091517229b06263028a9d38fcbbfc7f9617a8ec723ad7` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `Reach` | R6a cited | none | `4bbf4ddf1d0e0ef0c452f1676b3c8eb094a2ff27e4e1d188de38d9fbe880a231` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `reach_of_access` | R6a cited | `Quot.sound`, `propext` | `2a255b9b9fed8dbfa67b906d0f845ec066fd8c52562cd0b989f30fb51b0bfcb8` | `618f30a5387be060cf66c0af12a0a9006cc15302420949ba91e2550cd34b4f3a` | 40 |
| `reach_secEdges_map` | R6b cited | `Quot.sound`, `propext` | `c84a35a7532ca0931fa864e8db3500a99f748bf9621afa95af9b6f6cec2fc485` | `59743a647f7df18534ace2e241548bb5765a338534624edea01574a7836c4dd5` | 5 |
| `ReachedBefore` | R6a cited | `propext` | `8714b153269bca605a7bc21e586239a89118d2efebb0c8806ff025d32f8754b1` | `fb30db09a3bef5e3bcb639c2f203cdde265cd16377b34f558069bafa977324e7` | 4 |
| `readsOnly_examples` | R1 cited | `propext` | `63ed25e09d1ea11dcb15098d3b55342570f7703b536e302840ea11be7d44b6b4` | `9f434ba3e2c4519c078b380d074d48064d1e0b60ba2943dd26b0af9eefbea862` | 8 |
| `registry_examples` | R6a cited | `Quot.sound`, `propext` | `f81a0583cdc7f7558b703abb312862f759194aac8839a797a7065666ead9261e` | `4457b02da3db4eab0fd2fdda1bf43179cf4948c69480b24eeb93a3f523fec00e` | 33 |
| `registry_iff_cex_edge_into_entry` | R7f cited | `Quot.sound`, `propext` | `1e69a0407eb3f829bcbdc6595b94326972626a1a1ea9ee451525f5573dceb6cb` | `73418e1c677f3115f7d9dc967551216ab15de18b247f97335504232fba3c0dff` | 31 |
| `registry_iff_cex_other_name` | R7f cited | `Quot.sound`, `propext` | `9a043b2dd8781039595b0e9b705e2b4d23a5aeed397bf05fb75f0e9155f27761` | `73418e1c677f3115f7d9dc967551216ab15de18b247f97335504232fba3c0dff` | 31 |
| `registry_keep_or_retain_kept_precise` | R7f cited | `propext` | `39836f09b55aad19c71fe60a8017f1f3395488c20b656bff814143ff97f74fc6` | `b05491dec3efa5eaf5ab2ed189c92a2c991d801b0b4e8075ccf6de3f7a5df090` | 31 |
| `registry_nonvacuity` | R7a cited; R7a nonvacuity; R7f cited; R7f nonvacuity | `propext` | `b0c85562596e54432241de55b49b58c69d9d895175d6374d91aebe2258cad340` | `aeb3fab250074a22c8acca111742b68857b80daaf8a504f522e6265868966e3a` | 19 |
| `registry_precise_link_failure_conservative_kept` | R7a cited; R7f cited | `Quot.sound`, `propext` | `26141245ab8637aeea5ff021fef60115c1cf987ead5f9b86d57ecbb46a7c3e5f` | `1e366d992d619bfaf87039a6a992a52578b0f1d5ab8b8d276900b997cb3652ca` | 32 |
| `registry_precise_silent_shrink` | R7a cited; R7f cited | `Quot.sound`, `propext` | `c7b7a8592ebd6dc656eec7bd6a872e76384dcd336c2c4c88fafd09d71b351594` | `1e366d992d619bfaf87039a6a992a52578b0f1d5ab8b8d276900b997cb3652ca` | 32 |
| `RegistryKept` | R7f cited | `propext` | `7517adeb91c36f2944cf60e9593bb0a3ccb4f914198a74e388fea0c7dc29fd21` | `e5ad74fa4572e1e41ad967dd5c474b67f6fcbc85ca22618734d8e4fc2af68ed4` | 7 |
| `registryKept_iff_cex_edges_into_entries` | R7f ce:hN | `propext` | `12716ded2ebf09a4cef19709853888cf8eb83cf2a7316daa851e7e3a42c83c60` | `715fb0ac44f78563665c21c02b73fb23ce90f622e3ab323ab97d86361cf5aa41` | 32 |
| `registryKept_iff_of_noEdgeIntoName` | R7f result | `Quot.sound`, `propext` | `52ad545da96177c142bb4fcb21a234c7acabadab5b771b805696a24cb6985917` | `7183ff7d17681330b4c2e32af494164bb67ddf0b74a092e73883d7463110366e` | 30 |
| `registryKept_of_entries_rooted` | R7f cited | `propext` | `0897d7e4debe9cd85d57743371efe3cc4bf3e681385d0b00d0a9b5addff285fc` | `dd84b1694f771bda657d6d982c1d23f103b2a1fb961516a62193257015ec197f` | 29 |
| `registryKept_of_entries_rooted_nonvacuity` | R7f cited | `propext` | `8803a6dc70724b16c43cfa040984856833100dd0df1b182fb472b305a8670f17` | `b2d65faedf57ce0d8d2084acf20a6b94c72d76c888cd09d12682d144185f805e` | 17 |
| `registryScan` | R7f cited | `propext` | `1952cc8bd13b1a981a5905c0168db4008daed9123f5f2c01ec565a8f865de3b5` | `f7963d3fbe98420a4fd9154f290165cb7ab8b2372b1ac631f99c5732f4a63fa3` | 8 |
| `registryScan_examples` | R6a cited | `propext` | `37ad650e03e2c9c896f7d1c0f12d7d93e02f50ea0bc0870f3fb05646b40b0514` | `5f47c183919d03276c02211d910f34edcce682acf58760afe21c020bc57c3d8f` | 14 |
| `registryScan_preserved_examples` | R6a cited | `Quot.sound`, `propext` | `5efc00a85a3cf2cd286aabd69603e63f3ea0e02592fccf6225deb7f297ef2608` | `0070b50ae8c137ba7647d5aa7916d1cf83223fe0f357ed12e930c03fe673f4aa` | 40 |
| `Reloc` | R5a cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Reloc.AddressOnly` | R5a cited; R5c cited | none | `26d5d6ce4e2a120265aaa9e7b36681c6c7adbf3ebd186dd43e4ef6fd279247bd` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `Reloc.ReadsOnly` | R5c cited | none | `d38a0674db51a87952bdce8434b1d4b92428c297800257b01a1d41e278187425` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `relocationOrder_nonvacuity` | R5c cited; R5c nonvacuity | `propext` | `114d08d4523c2789d297915ed53ac83b88800aa08ce3260a7fbb7611d9aa9101` | `550fae3e50e578d6f7309a7b9039eb89d33c89ecc3512baa0dbb955c9aab9031` | 14 |
| `RelocSlotsWritable` | R1 cited; R3c cited | `propext` | `7960ad8d7d2d8810f18fea41765c15f95bd8f3769e875639c9d7faa5982fbb3e` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `relro_slot_cex_load_fault` | R2d cited | `propext` | `9c0c84b4d773fd4c4a75a9a90aaf098696de959f6333f3f3cf3fc83423f88f9d` | `43f19978c28c702631d1e2d1850d5f2684b2c421e63ec550c204de9b8f602203` | 72 |
| `relro_slot_cex_mut_slot` | R2d cited | `Quot.sound`, `propext` | `224a8f900fc652d73dfcacd99ee8e1c92d4d0e773a10b10f23dd161182a26aea` | `950ee524cc3341ba7557c1d86c5a371425771c7a5c4f2058c390f37467233581` | 71 |
| `relro_slot_cex_no_cover` | R2d cited | `Quot.sound`, `propext` | `ae63c3a683fcf70c8f44259dfb713fbf6354f541e9bde5c22dfe28b365dfae68` | `b979204554aef3379347269b6d14e2cc382d3bb79d99485b789dcb51f7530913` | 73 |
| `RelroIs` | R4a cited; R4b cited; R4c cited; R4d cited; R4g cited | `propext` | `b7ec7398df5cd4f1415de50b38c63094bbab59f74f832f81fc560f5329d15542` | `cb15c1882adc9862c7fb30c2e484994dd974797de0ba1cd8c24dcbb66f0b1181` | 5 |
| `relroIs_examples` | R1 cited | `propext` | `d5156a6bb9d4b872fc97727a2a1470c4d9a9177431356f056cbda972a2bffc8b` | `f476a706708ba3da9e8b34c7e5b74c691f1d78a5e3dd0caae35d385f980645d5` | 8 |
| `resolver_overwrites_addressOnly_slot_order_dependent` | R5c ce:hR | `propext` | `954fd71da1ad98385fd156d25e2b5bf585bae79f95f723e075479ddf85854f61` | `4501e4064ee846f1abdafb1a0de6df9f805934fdc3808c906b308f1e69300775` | 17 |
| `resolver_reads_unrelocated_slot_order_dependent` | R5a ce:hA; R5c cited | `propext` | `dea99dbfddd5b556ed2d98d7ef12176a16bdafb367097944775101c68c1a33ba` | `ec621a80e6cdea7991b491f4d8cba9b018fd1c67045813ff83e1c88c4a5e2db4` | 15 |
| `resolverOrder_cex_not_permA` | R5c ce:pA | `Quot.sound`, `propext` | `53365bd0a63194b8b6ab7a71714f2ef8001e4b694774f1791935264c79307695` | `884af3c3654d3186576d25afe5152ad85df4bb6956776fe9687c924abe97691c` | 15 |
| `resolverOrder_cex_not_permR` | R5c ce:pR | `Quot.sound`, `propext` | `cc7bb8ed1626eeabc3948891ebb5a38375924ff5397b9e1b46eaca2eaac3fc2c` | `884af3c3654d3186576d25afe5152ad85df4bb6956776fe9687c924abe97691c` | 15 |
| `resolvers_read_resolver_slot_order_dependent` | R5c ce:hR | `Quot.sound`, `propext` | `7bc3ca7ca4a452632cc9eaaf9442b07a306d73b6c96a877d5c769514d27184d5` | `d38715c4080bd75b1fb5652e3f5ad5f331caae7f0e31f425b290e420f765d040` | 15 |
| `resolvers_same_slot_order_dependent` | R5c ce:hNR | `Quot.sound`, `propext` | `6b2201c796f9e9c15c93a804898db39a059edf78a850d8d961cf5e154218e326` | `01d1864eb400dcf0ab09381fefb38054b4cc7c9317c41a47f608a2c9cc47f07d` | 14 |
| `retained_but_compiler_dropped` | R8b result | `propext` | `883a2ff41f8bc2d892149810c4f90c2aeda092e0896c7abaf31145d8f495ed12` | `05f8110fbb2e2a91ea0a1aabbc4d41cd42ae2f50ea445dc0ec8c637ae399d468` | 22 |
| `rooted_cex_unrooted` | R7f cited | `Quot.sound`, `propext` | `8edd7eaff41b828ce64c86e90cfdbda842d2a8a6f1f1c106c11ca70bc0e48202` | `b05491dec3efa5eaf5ab2ed189c92a2c991d801b0b4e8075ccf6de3f7a5df090` | 31 |
| `roundedMask` | R4a cited; R4b cited; R4c cited; R4d cited | none | `296b4a9827b4a2caa880f18a1ad76677e0fa7c94f67c9731da163d1a931682ea` | `a6bf2215e6eaecb24a3bdd26f2ad4fbe12136ed3fc255a5edc1dec525adb6d6c` | 4 |
| `roundedMask_downUp_pageGranular` | R4d cited | `propext` | `69bd67270c6e3ea578134223083e1592bd09fccca22a5087d53308e44ad1c10e` | `543019a395e77d4f98cfefa7fcea14085275a70a746bd7852fb875391e1ff8ee` | 12 |
| `roundedMask_empty_examples` | R1 cited | none | `d7ae1a9cc4521e67986fb950889b270c3b97ad8e70e40398e76aaf7835622465` | `a971502328a8ffcdd84c36578ca7537899c5e19a1b117ffc2bb99e3f59342180` | 11 |
| `roundedMask_eq_false_of_le` | R4c cited | `Quot.sound`, `propext` | `677713eb65e263db5ee1a91bfa0cfa0d280a77423f4b1e3634365dcc35233d86` | `a971502328a8ffcdd84c36578ca7537899c5e19a1b117ffc2bb99e3f59342180` | 11 |
| `roundedMask_examples` | R1 cited | none | `d5af7e56c9b87e356da63f00b88285264f68debcd1c1256a900e742bcb11eeb6` | `a971502328a8ffcdd84c36578ca7537899c5e19a1b117ffc2bb99e3f59342180` | 11 |
| `Rounding` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `rRes1` | R5a cited; R5c cited | none | `a2b9b39c81ddb775335091517229b06263028a9d38fcbbfc7f9617a8ec723ad7` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `rRes2of1` | R5c cited | none | `a2b9b39c81ddb775335091517229b06263028a9d38fcbbfc7f9617a8ec723ad7` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `rRes3of2` | R5c cited | none | `a2b9b39c81ddb775335091517229b06263028a9d38fcbbfc7f9617a8ec723ad7` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `rRes4of9` | R5c cited | none | `a2b9b39c81ddb775335091517229b06263028a9d38fcbbfc7f9617a8ec723ad7` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `RunPreserved` | R6a cited; R7f cited | `propext` | `6179da6d12fbe5a61bce9ac8b87a06a98b81b87a7602c3902ae8c3cae1c5c3eb` | `9da75f0f9d1634be9b5307e236c18bf15c87e3593d59a0c18d13a7d224eafd69` | 11 |
| `runPreserved_examples` | R1 cited | `Quot.sound`, `propext` | `52d8398669b5a7a038f150d0fb461d1a1983203301d10b6e3fe59f033322a475` | `f22d131b0b7497c3bedb049c68fc6fa6d3e5d5adfd21c5ff013bd54e1405f4d4` | 38 |
| `runPreserved_of_edgeAccessesFollowEdges_of_implicitAccessesHitRoots_of_boundsAccessesRetained` | R6a result | `Quot.sound`, `propext` | `75ef20f38f70d6e85a3842fc0dc7b90a82424138768c6e6a11b1ddb28dc28681` | `bd690a392f2cda20a2fb85cecbe40112aaf92a7f55248ff177e98a72e12d4654` | 41 |
| `runPreserved_registryScan_iff_registryKept` | R7f cited | `Quot.sound`, `propext` | `77321d1ef3f3ac3aefd96c62fec05bd4ea4e130d89a3b76b4e2f3dc65f61a60f` | `beb08cf4f554c3707d3bcf4e088f709510104ff1e641644281d918b7ac97e9df` | 39 |
| `runT` | R1 cited | none | `8a8714ffae8d1cc622ba4850a307a80252b8653e6a29bfdbd3c6508f6bc9b6fa` | `9f72ede4a7f0df8bc9b8711c7bc03d58b223eb6c75ca688a7413b16a15485dc2` | 27 |
| `sa0` | R1 cited | none | `748c9225a4e5b5cb5bfd324756cb652253733aef61cd92e9b4b3c17d17452f51` | `1743cc1cc1f051fee6e11039d273a23dc1b686abc76afc134f8ea9f46fd4250c` | 2 |
| `Sec` | R6a cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Sec.isRoot` | R6a cited | none | `5a68abc861ecd4c51dcf05338e38bf8ee490e9fa8f3bb6369ce197d81d5d48ae` | `706b28667cb4d8d67efba8614f296810f4bbd0eceafa6a741c409d4443bfbf72` | 2 |
| `sec_isRoot_examples` | R6a cited | none | `87da9b47b219f855c5c58b19500b45f22c45545f3fee7db30680f9d2de6296e3` | `3af7af16f498bccb163ff9404e446dcf32a37cbcfe46b79e010b909c6883b255` | 8 |
| `secEdges` | R6b cited | none | `c62f88c216107c65905a9b31e1f2d297cefe2faf7822f1502d577fbaeac54bfc` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `secFine` | R6b cited | none | `01e52fc1704581a452740b56a23f83cac77adcf37ca5cafa352d4fbcfb4a071f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `secRoot` | R6b cited | none | `b16bc3bc4b3ccd7b45f680fb51a95ba57e8be164081f67d9e4767734e8a99ac2` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `secShared` | R6b cited | none | `01e52fc1704581a452740b56a23f83cac77adcf37ca5cafa352d4fbcfb4a071f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `srcReach_examples` | R8b cited | `propext` | `7dd32075d02cc0266f89df11728c775a1bba213a77e03d4ea541e66284bfe31e` | `9301c5a89633a29874ba341bc680f90aecc0a68a65b2d3a3983d6f19a0c21596` | 14 |
| `ssEdges_examples` | R1 cited | `Quot.sound`, `propext` | `cee34a3304c1f7cdbccb5542c51c9f48d7a61c3010a50d2dcbd724844730df08` | `67f62dbf3320207625f9b5bfcd32e1bfd682536f87f831091997fa0611cd16fd` | 17 |
| `SSPolicy` | R6a cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `St` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `StartStopUndefined` | R7a cited | `propext` | `7517adeb91c36f2944cf60e9593bb0a3ccb4f914198a74e388fea0c7dc29fd21` | `e5ad74fa4572e1e41ad967dd5c474b67f6fcbc85ca22618734d8e4fc2af68ed4` | 7 |
| `Static` | R8a cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `stepApply` | R1 cited | none | `405220ecc5dcc8ab5d4e289b16551fc9cf6af3f7d51efc3abb353b880e1c0437` | `55362b7dc9ca0e3862171c94f10bd10f180ca292aa4a2e4eb9a6fde388cc9b34` | 11 |
| `stepOp` | R1 cited | none | `ce0920d3425139eee249572e4b8619f307c635d0785c03625a5c7865f62e20fc` | `c64806b6d311e3140ee4496d08c12c7a623050e924b81bdf7a322c67c5d196db` | 21 |
| `stepProtect` | R1 cited | none | `2250fe6d1dde2a69093e8b97fc899a9614fed84a757903edf6f2cacb30b42acc` | `43d836c6f85610e69207a4fbe1a89c51d300582d77ee889f4cdf7fd029cca98a` | 14 |
| `stMain` | R8a cited; R8b cited | none | `cd47a44c149a529bea278644848d3eddefcdddd7bc18589aadce39026a07704f` | `f5bb185b0467333d01f14914557e6bf2c068bba3841d2ac6915bfad8679586d3` | 2 |
| `stPlain` | R8b cited | none | `cd47a44c149a529bea278644848d3eddefcdddd7bc18589aadce39026a07704f` | `f5bb185b0467333d01f14914557e6bf2c068bba3841d2ac6915bfad8679586d3` | 2 |
| `stRetainOnly` | R8b cited | none | `cd47a44c149a529bea278644848d3eddefcdddd7bc18589aadce39026a07704f` | `f5bb185b0467333d01f14914557e6bf2c068bba3841d2ac6915bfad8679586d3` | 2 |
| `stUsedOnly` | R8b cited | none | `cd47a44c149a529bea278644848d3eddefcdddd7bc18589aadce39026a07704f` | `f5bb185b0467333d01f14914557e6bf2c068bba3841d2ac6915bfad8679586d3` | 2 |
| `stUsedRetained` | R8a cited | none | `cd47a44c149a529bea278644848d3eddefcdddd7bc18589aadce39026a07704f` | `f5bb185b0467333d01f14914557e6bf2c068bba3841d2ac6915bfad8679586d3` | 2 |
| `survives_conjunction_cex_without_lookup` | R8a cited | `propext` | `3af59c0bbabca0c1f1b9d15fc3c3611f96840474ad19dcca363a0d8f4db8fd10` | `65e88eb66d21105a8737585ef85eb93b5e0a10df75776357d0f072c6b84ce6ac` | 21 |
| `survives_iff_compiledPath` | R8a result | `propext` | `d01d83624c5b8af34f431fdcb4ccf2e2c5a317f579f0ab528e4f86007b87f667` | `7db88ee37f893446f2785d4b9ecc534585fbc3b4188289a6a668ce0476d975e9` | 23 |
| `survives_iff_compileKept_and_linkReach_or_retain` | R8a cited | `propext` | `2040ec5ea4456a6ac3249022da97c7b1dd045112cb3dec419efca5766b6c9ee4` | `ab63ca1042cf6b3a1ce92d236766bdcf34a7da55ead080863e5dd45b2706b01d` | 20 |
| `survives_iff_linkReach` | R8a cited | `propext` | `60172318a3053c563a90e97b857ba48121e7a397ce8d148abdbd526d985e8cf5` | `ab63ca1042cf6b3a1ce92d236766bdcf34a7da55ead080863e5dd45b2706b01d` | 20 |
| `Sym` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `symReloc` | R2d cited; R5a cited; R5c cited | none | `3e266ae898e17ab6a443e6db3c09b23d4f3b23b2be500619e3c39488c6852ef4` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `SymTab` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `timeline` | R1 cited | none | `c2b258cbec777ae622d88bfff09635b89a6dee54394d31957b4c43890a11f314` | `7d00745bc23faf960624ea2f113de613d3295ebe957ee460a852a920eff9c27c` | 19 |
| `Trace` | R1 cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `trace` | R1 cited | `propext` | `bc0838a5d83645f6ce903583acc24e5ed2acabb1ccc130960b8a742e46ba949d` | `7453f54d9cdc28100339835bc6ba9e6b199409d805615bad844428b13b64ea72` | 25 |
| `trace_twoPhase` | R1 cited | `propext` | `250fe1c49bead68db6021c7be50175b64d5eb197944fe02ab05f140c891940d1` | `9f09707798d5e40fa47226420b72ab13ed26bebdd3e73e7447c5edc01277fbfb` | 66 |
| `tryApplyAll` | R1 cited | none | `c18b47f748d3d6a35713b38993ec42ced852a52881d3ff5578668fdbad9ea9bd` | `a9b9b1928bfb0be288eb77cc99192bc8a8d4d84e552c8f8950d42bcbd6661405` | 5 |
| `tryApplyAll_bind` | R3c cited | `propext` | `ee4f07e9c29db70e73e639bce866cad8f208fdd39f7492ce533e377e9c1fe348` | `21098cc998e6be206c979817d4b62d48a9a4d486f1097e857a2706becd0f3def` | 11 |
| `tryApplyAll_other` | R3c cited | `propext` | `9051eb200b686dd14121e2232360d5fa58d4eb540eeeab68526e8dc7ca4e8ee8` | `0bbb09a7b627eff1973c5d72ba3d05936ee30f821b916b70e49d866907795204` | 10 |
| `twoPhase` | R1 cited | none | `5ffb29b0371b67f70bc6111c4e9ba08c77a04a47e19b00353a1422c4344cd589` | `7d00745bc23faf960624ea2f113de613d3295ebe957ee460a852a920eff9c27c` | 19 |
| `twoPhase_cex_prot_covers_mut` | R1 ce:hAvoid | `propext` | `ac346df7f20ecf325b1a8c70453b44419de8202e9a65a2e818515d414ca081e9` | `3555823376e91b95ca52ad558805ebbe907600a31f98a785bb70e26aad38f95e` | 78 |
| `twoPhase_cex_prot_misses_relro` | R1 ce:hCover | `propext` | `426d0b6bebf5b09df0a0cb1f3e41fb96116644b7402825a11f7dde96b7f4dd2c` | `ab19088a0a3bd8691b5e08862335c5a729172f7a05de6df8c255ba3cab4eb7db` | 78 |
| `twoPhase_cex_protect_after_entry` | R1 ce:hOrder | `propext` | `42d3c4ee94009d317ea2fba225bc12e8080e74201778f0a2eae4ca44535b89ae` | `af6cef94475543f05e057e80ee2dfdadbd7bb19fdeb9e2a34c8ce48cc6e4268b` | 77 |
| `twoPhase_cex_protect_before_last_reloc` | R1 ce:hOrder | `propext` | `ad4f37768623ee7b3e76083d6915be1e7965a1936fb55c1879835b89bf6ab761` | `640b66ae735487e4cf846c068706d7ff82e9f69fd15b0f3fcbbaaee1e31f2223` | 77 |
| `twoPhase_cex_slot_not_writable` | R1 ce:hWr | `propext` | `873bb0ea6e8e6d06ed8bd1290e060cc90d832889757739edd780cc1152f3cc4f` | `75d4d43cc8e1cf62847900ca003cd7704515272847a406daf62a813e03210189` | 78 |
| `twoPhase_nonvacuity` | R1 nonvacuity | `propext` | `0a4ee30bfca93cffc21c36b9fe3b20f9610cdb0a39e337c9776e29ceac7a2aca` | `459ea0de1d77729f0c5c94cac7e48620a314999ac64023725f889bbeebe4a9ae` | 31 |
| `TwoPhaseGuarantees` | R1 cited | `propext` | `d170b99684c45e8472ab8d172df05c4cfb6721710303470c5d49add8afd09612` | `42e8b2bd7af6fe0786d6de48bfe6270813f020cc0c81e046da36344ae91cc084` | 15 |
| `twoPhaseGuarantees_examples` | R1 cited | `Quot.sound`, `propext` | `b823c1d0af434cce5bee18428e2332c353a810c9dde2bf974e00b38366ff33d0` | `73312f9e2f18f6fe4f3bb72342f422bc41caf67005f21952831f1444e546051c` | 72 |
| `twoPhaseGuarantees_of_slotsWritable_of_protectAfterRelocs_of_covers_of_avoids` | R1 result | `Quot.sound`, `propext` | `88bc8b8deeeefaaabfcedfa3b6b69b98add162f3c5c7766e0e513dc24d1e1de1` | `9b144e3130586a639f5c4b7c13db45e57cd1b6deb2d79ddef29f272d682c3c2f` | 73 |
| `twoStage_examples` | R6a cited | `propext` | `523a5e46ca3e644e3b2be87587ccc5f0613b815fe72dd142731c70d067133796` | `b0c5faad6243cb94f11219fc5a995b0af889c82093839768b4c86e972db8d873` | 24 |
| `twoStage_nonvacuity` | R8a cited; R8a nonvacuity | `propext` | `02e380e92adddf8b32714e76695a08145b2216a11768ebeeb343e9079479c019` | `6d0a08325ade5f8897fe1bbfa015d0aebdb9129f5fb7bca2e38560363bbd2970` | 25 |
| `unreferenced_item_kept_when_sharing_live_section` | R6b cited; R8a cited | `Quot.sound`, `propext` | `78f2263cf08808928d517522ea3c482001255f210c98abc9699e5c5a6b65f22f` | `5bdd9b940335e1bcd121fd3d17cae855e58d38e60c5a0d926518cfde2267f043` | 10 |
| `upd` | R1 cited | none | `9ea47864dd1e33c4c7791ff96a8aa81d14143a5f4c67ada06ad40f18a1c16402` | `fdd79700fbe7f143e60825aa1fa91d578454c7d3e1e3ed5c219fc737b36a6baa` | 1 |
| `WriteFaultsAfter` | R3a cited | `propext` | `d734f99d9d50b3309a43d7bbe1cb8cf31e841c4dd69e5bc582c5951cd45f3aae` | `b3674e0a76ed34e5f623750d0c20dffc179169f01adbcf6395626b24a34230d1` | 12 |
| `writeFaultsAfter_examples` | R1 cited | `Quot.sound`, `propext` | `43617ac3140b94a4f3c09cdb90247e06b1aef0802798943314c7f27952db8d7e` | `b1c5bc9222394bab783ffd86ca5567ecb2fc4a92ce19c0d6b4c3984bf31be9e2` | 69 |
| `writeFaultsAfter_iff` | R2d cited | `Quot.sound`, `propext` | `06767e1a737da1b96873a3dfcdafe828c47e8aba510a757ecfe88ee3ac2c49a5` | `b0c56322f2edf5b2ad44268d7ce16177cc3eae4ecadf245715ebbd836bbf3c03` | 65 |

### Primary sources

Full quotations, with exact line ranges at the pinned revisions, are in the prior-art entries of each card under Findings. Retrieval record (accessed 2026-11-21):

Every quoted line range was located in a copy of the source fetched at the stated revision; for git-hosted files the
blob hash of the copy matched the hash the host reports for that path at that commit.

* binutils 2.42: tag `binutils-2_42` = commit `c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9`: `ld/ld.texi` (lines 1478-1482,
  1537-1542, 1558-1563, 1592-1607, 2030-2039, 2047-2048, 5462-5466, 5506-5512, 7324-7339) and `ld/NEWS` (lines 142-143).
* binutils 2.36: tag `binutils-2_36` = commit `9288e0fae61b716ce75334be906283de8b18b787`: `ld/NEWS`, `gas/NEWS`.
* LLVM 19.1.0: tag `llvmorg-19.1.0` = commit `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4`: `lld/docs/ld.lld.1`,
  `lld/docs/ELF/start-stop-gc.rst`, `lld/ELF/Writer.cpp`, `llvm/docs/LangRef.rst`,
  `llvm/lib/Target/TargetLoweringObjectFile.cpp`, `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp`,
  `clang/include/clang/Basic/AttrDocs.td`.
* glibc 2.40: tag `glibc-2.40` = commit `3d1aed874918c466a4477af1da35983ab036690e`: `elf/dl-reloc.c`, `elf/do-rel.h`,
  `elf/elf.h`.
* musl 1.2.5: upstream repository `https://git.musl-libc.org/git/musl`, tag `v1.2.5` = commit
  `0784374d561435f7c787a555aeab8ede699ed298`: `ldso/dynlink.c` (git blob `324aa85919f0fdef3156ec36774be2c55ba1d3a4`).
* FreeBSD: branch `releng/14.1` at commit `f389e68ca980b7e053a34d9eddde89b4c2a1ee6c` (branch head at retrieval).
* Android Bionic: `aosp-mirror/platform_bionic` branch `android14-release` at commit
  `e4df46f213d8d363017dce7ded5d1f2159614425`.
* GCC 11.1.0 manual: tag `releases/gcc-11.1.0` = commit `50bc9185c2821350f0b785d6e23a6e9dcde58466` (`gcc/doc/invoke.texi`,
  `gcc/doc/extend.texi`), and the online HTML pages.
* Rust Reference: rust-lang/reference commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/abi.md`; rust-lang/rust issue
  93798 (an open tracking issue; living document, body snapshot 2026-11-21; background only, not a subject).
* Background (living documents, snapshots 2026-11-21): F. Song, "GNU indirect function", "Linker garbage collection",
  "All about Global Offset Table", maskray.me.
* Bibliographic records verified via Crossref: Bernstein 1966 (doi:10.1109/pgec.1966.264565), Morrisett, Felleisen and
  Harper 1995 (doi:10.1145/224164.224182), Gammie, Hosking and Engelhardt 2015 (doi:10.1145/2737924.2738006), Wang, Xu,
  Wilke and Shao 2020 (doi:10.1145/3428265), Kell, Mulligan and Sewell 2016 (doi:10.1145/2983990.2983996). Paper texts
  were not re-read for this package except Kell et al.; descriptions of the others rest on their titles and on secondary
  summaries, as each entry states.
* **Not verified:** the Linux Standard Base Core text for `PT_GNU_RELRO` (the hosting site served an automated bot-check
  page, which was not bypassed); Ian Lance Taylor's original post, quoted inside the Bionic source comment.
* **Novelty search** (bounded: web search and Crossref): no mechanized model of RELRO page rounding, GC retention roots,
  or compiler-then-linker retention found; closest are the Kell–Mulligan–Sewell static-linking specification and
  CompCertELF, neither of which models dynamic loading, RELRO protection or `--gc-sections`. Tiers are T0 or T1; no T3
  claim is made.

**Identities of pinned sources** (rechecked 2026-11-21 against the hosting service): Lean 4 `v4.34.1`: GitHub `leanprover/lean4`, lightweight tag pointing at commit `5045d0056413266e57c625dcd7c365b10e377c52`. binutils: `sourceware.org/git/binutils-gdb.git`, tag `binutils-2_42` at commit `c7f28aad0c99d1d2fec4e52ebfa3735d90ceb8e9` and tag `binutils-2_36` at commit `9288e0fae61b716ce75334be906283de8b18b787`. LLVM: GitHub `llvm/llvm-project`, tag `llvmorg-19.1.0` at commit `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4`. glibc: `sourceware.org/git/glibc.git`, tag `glibc-2.40` at commit `3d1aed874918c466a4477af1da35983ab036690e`. musl: `git.musl-libc.org/git/musl` (web view `git.musl-libc.org/cgit/musl`), tag `v1.2.5` at commit `0784374d561435f7c787a555aeab8ede699ed298` (the tag's commit feed lists that commit, "release 1.2.5", as its tip; `ldso/dynlink.c` at the tag is git blob `324aa85919f0fdef3156ec36774be2c55ba1d3a4`, and the quoted lines were read there). FreeBSD: GitHub `freebsd/freebsd-src`, commit `f389e68ca980b7e053a34d9eddde89b4c2a1ee6c` (head of `releng/14.1` when the source was retrieved). Android Bionic: GitHub `aosp-mirror/platform_bionic`, commit `e4df46f213d8d363017dce7ded5d1f2159614425` (`android14-release`). GCC: GitHub mirror `gcc-mirror/gcc`, tag `releases/gcc-11.1.0` at commit `50bc9185c2821350f0b785d6e23a6e9dcde58466`. Rust Reference: GitHub `rust-lang/reference`, commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`.

## Revalidation

Requirements: `elan` (the Lean toolchain manager, so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The Lean project has no dependencies (no Mathlib, no `[[require]]`).

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and there (1) runs `lake build`; (2) scans every Lean source of the package for `sorry`, `admit`, `native_decide` and `axiom` declarations; (3) runs a generated Lean program that calls `Lean.collectAxioms` on every declaration of the library `ToyRelroGc` and fails if any axiom other than `propext`, `Classical.choice`, `Quot.sound` occurs; and (4) for every Lean name referenced by `results.json` or recorded in `audit/statements.json`, recomputes `statement_sha256`, `closure_sha256` and `closure_size` exactly as described under Evidence ("What is hashed") and compares them with the recorded values. It prints `REVALIDATED` and exits with status 0 when every check passes, and with a non-zero status otherwise.

Manual build and axiom spot check, run from the package directory (the file `lean/AxiomSpotCheck.lean` is not part of the library target and contains one `#print axioms` command for each Lean theorem of each result):

```sh
cd lean
lake build
lake env lean AxiomSpotCheck.lean
```

Each `#print axioms` line must report at most `propext`, `Classical.choice` and `Quot.sound` (or that the theorem depends on no axioms).

A passing run establishes that the recorded statements still build and kernel-check with the recorded axioms under the pinned toolchain; it re-establishes nothing about real systems. Under a different toolchain the statement hashes may change even when the mathematics does not (they hash Lean's `repr` of terms); in that case compare the statements in `lean/ToyRelroGc/` with the ones quoted under Findings by reading them. The modeling-bridge claims and the quoted external sources are not revalidated by any command: to recheck a quotation, re-fetch the source at the repository, tag, commit and line range listed in the card's prior-art entry and under Evidence ("Primary sources"), and compare the quoted text.
