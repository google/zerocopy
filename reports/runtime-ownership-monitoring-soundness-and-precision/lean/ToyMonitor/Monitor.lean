import ToyMonitor.Strategy

/-!
# Programs, the ownership monitor, and the static meaning of contracts

Programs are straight-line: byte reads and writes, sequencing, calls to annotated
callees (contract `pre`/`post` plus the callee body, inlined as a subtree), and calls
to unannotated callees.

* `exec` is the plain (uninstrumented) execution; it is total and deterministic.
* `monitor` is the run-time ownership monitor: per-byte ownership map
  (address ↦ owning frame, frames identified by call depth), ownership transfer on
  call/return computed by a footprint strategy, ownership checks on every access of
  instrumented code, and an optional leak check at return. Unannotated callees are
  either instrumented (checked as inlined into the caller's frame) or trusted (their own
  accesses unchecked; annotated callees they call are still monitored).
* `Satisfies` is the static (separation-logic) meaning: every call's transferred
  fragment satisfies the precondition, the callee only touches what it was given,
  and on return the callee's whole fragment satisfies the postcondition — with the
  footprints chosen angelically (existentially, per call).
* `SatisfiesBy s` is the same with the footprints chosen by the strategy `s`.
-/

namespace Toy.Monitor

/-- Straight-line programs with annotated and unannotated calls. -/
inductive Prog where
  | skip
  | read (a : Addr)
  | write (a : Addr) (v : Val)
  | seq (p q : Prog)
  /-- Call to an annotated callee with contract `pre`/`post`; `body` is the callee. -/
  | call (pre post : Assn) (body : Prog)
  /-- Call to an unannotated callee (no contract); `body` is the callee. -/
  | unannot (body : Prog)

/-- Plain execution (no checks). -/
def exec : Prog → Heap → Heap
  | .skip, h => h
  | .read _, h => h
  | .write a v, h => h.write a v
  | .seq p q, h => exec q (exec p h)
  | .call _ _ body, h => exec body h
  | .unannot body, h => exec body h

/-- All contracts (pre- and postconditions) occurring in a program. -/
def Prog.contracts : Prog → List Assn
  | .skip => []
  | .read _ => []
  | .write _ _ => []
  | .seq p q => p.contracts ++ q.contracts
  | .call P Q body => P :: Q :: body.contracts
  | .unannot body => body.contracts

/-- Per-byte ownership map: address ↦ owning frame (frames are call depths). -/
abbrev Own := Addr → Option Nat

/-- Initial ownership: the top frame (depth 0) owns exactly the listed addresses. -/
def initOwn (O : List Addr) : Own := fun a => if a ∈ O then some 0 else none

/-- The fragment of `h` owned by frame `d`. -/
def frag (h : Heap) (o : Own) (d : Nat) : Heap := fun a => if o a = some d then h a else none

/-- Move ownership of the listed bytes that are owned by frame `src` to frame `dst`. -/
def transfer (F : List Addr) (src dst : Nat) (o : Own) : Own := fun a =>
  if a ∈ F ∧ o a = some src then some dst else o a

/-- Monitor configuration.
* `leakCheck`: at return, fail if any byte transferred to the callee is still owned
  by the callee after the postcondition's footprint has been returned.
* `checkUnannot`: `true` — unannotated callees are treated as inlined: their accesses
  are checked against the caller's frame; `false` — unannotated callees are trusted
  (not instrumented): their own reads and writes are not checked, but annotated callees
  they call are still monitored as usual (contract transfer on call and return, checked
  accesses inside the annotated callee). -/
structure MonCfg where
  leakCheck : Bool
  checkUnannot : Bool

/-- Leak check on, unannotated callees checked as inlined. -/
def MonCfg.strict : MonCfg := ⟨true, true⟩

/-- The run-time ownership monitor with an explicit instrumentation mode.
`monitorAux cfg s chk p h o d` runs `p` from heap `h` with ownership map `o` in frame
`d`; `chk = true` means the code being run is instrumented (its reads and writes are
checked against frame `d`), `chk = false` means it is trusted, uninstrumented code. It
returns the final ownership map, or `none` if some check fails. Heaps are the actual
heaps of the plain execution `exec`.

Annotated callees are always instrumented (`chk = true` in their bodies). An unannotated
callee runs in its caller's frame and stays instrumented exactly when its caller is and
`cfg.checkUnannot = true`. -/
def monitorAux (cfg : MonCfg) (s : Strategy) : Bool → Prog → Heap → Own → Nat → Option Own
  | _, .skip, _, o, _ => some o
  | chk, .read a, h, o, d =>
    if chk then (if o a = some d ∧ (h a).isSome = true then some o else none) else some o
  | chk, .write a _, h, o, d =>
    if chk then (if o a = some d ∧ (h a).isSome = true then some o else none) else some o
  | chk, .seq p q, h, o, d =>
    match monitorAux cfg s chk p h o d with
    | none => none
    | some o₁ => monitorAux cfg s chk q (exec p h) o₁ d
  | _, .call P Q body, h, o, d =>
    match s P (frag h o d) with
    | none => none
    | some F =>
      if F.all (fun a => decide (o a = some d)) then
        match monitorAux cfg s true body h (transfer F d (d + 1) o) (d + 1) with
        | none => none
        | some o₂ =>
          match s Q (frag (exec body h) o₂ (d + 1)) with
          | none => none
          | some F' =>
            if F'.all (fun a => decide (o₂ a = some (d + 1))) then
              if cfg.leakCheck &&
                  F.any (fun a => decide (transfer F' (d + 1) d o₂ a = some (d + 1))) then
                none
              else some (transfer F' (d + 1) d o₂)
            else none
      else none
  | chk, .unannot body, h, o, d => monitorAux cfg s (chk && cfg.checkUnannot) body h o d

/-- The run-time ownership monitor: the top-level program is instrumented. -/
def monitor (cfg : MonCfg) (s : Strategy) : Prog → Heap → Own → Nat → Option Own :=
  monitorAux cfg s true

/-- The monitor accepts the run of `p` from heap `h` when the top frame starts out
owning exactly `O`. -/
def Accepts (cfg : MonCfg) (s : Strategy) (p : Prog) (h : Heap) (O : List Addr) : Prop :=
  (monitor cfg s p h (initOwn O) 0).isSome = true

instance (cfg : MonCfg) (s : Strategy) (p : Prog) (h : Heap) (O : List Addr) :
    Decidable (Accepts cfg s p h O) :=
  inferInstanceAs (Decidable ((monitor cfg s p h (initOwn O) 0).isSome = true))

/-- Static (separation-logic) meaning of the contracts of a run: running `p` from `h`
in a frame owning exactly `O`, every access is to an owned allocated byte, and at
every call some footprint `F` of the precondition inside the caller's fragment is
transferred, the callee runs owning exactly `F`, and the callee's entire final
fragment (on `F`) satisfies the postcondition. Unannotated callees run in the
caller's frame. -/
def Satisfies : Prog → Heap → List Addr → Prop
  | .skip, _, _ => True
  | .read a, h, O => a ∈ O ∧ (h a).isSome = true
  | .write a _, h, O => a ∈ O ∧ (h a).isSome = true
  | .seq p q, h, O => Satisfies p h O ∧ Satisfies q (exec p h) O
  | .call P Q body, h, O =>
    ∃ F, IsFootprint P (h.restrict O) F ∧ Satisfies body h F ∧
      IsFootprint Q ((exec body h).restrict F) F
  | .unannot body, h, O => Satisfies body h O

/-- `SatisfiesBy s`: like `Satisfies`, but the witness footprints are exposed as the
ones computed by the strategy `s` — at each call, `s` applied to the caller's fragment
returns `F`, which is a footprint of the precondition, and at return `s` applied to the
callee's fragment returns `F'`, which has the same members as `F` and is a footprint of
the postcondition. -/
def SatisfiesBy (s : Strategy) : Prog → Heap → List Addr → Prop
  | .skip, _, _ => True
  | .read a, h, O => a ∈ O ∧ (h a).isSome = true
  | .write a _, h, O => a ∈ O ∧ (h a).isSome = true
  | .seq p q, h, O => SatisfiesBy s p h O ∧ SatisfiesBy s q (exec p h) O
  | .call P Q body, h, O =>
    ∃ F, s P (h.restrict O) = some F ∧ IsFootprint P (h.restrict O) F ∧
      SatisfiesBy s body h F ∧
      ∃ F', s Q ((exec body h).restrict F) = some F' ∧ (∀ a, a ∈ F' ↔ a ∈ F) ∧
        IsFootprint Q ((exec body h).restrict F) F'
  | .unannot body, h, O => SatisfiesBy s body h O

/-- Confinement of uninstrumented code, as an operational property of the concrete run.
`UnannotConfinedAux s u p h O`: running `p` from heap `h` in a frame owning `O`, where
`u = true` means `p` is (part of) an unannotated callee, every read and write executed by
unannotated code targets an allocated byte of the frame it runs in. Accesses of
annotated code impose nothing (they are checked by the monitor). Inside an annotated
callee the frame is the footprint `F` that the strategy `s` returns for its precondition
in the caller's fragment (for every such `F`); an unannotated callee runs in its caller's
frame. The predicate mentions only access targets, allocation, and the strategy's
footprints — not the contracts' satisfaction. -/
def UnannotConfinedAux (s : Strategy) : Bool → Prog → Heap → List Addr → Prop
  | _, .skip, _, _ => True
  | u, .read a, h, O => u = true → a ∈ O ∧ (h a).isSome = true
  | u, .write a _, h, O => u = true → a ∈ O ∧ (h a).isSome = true
  | u, .seq p q, h, O => UnannotConfinedAux s u p h O ∧ UnannotConfinedAux s u q (exec p h) O
  | _, .call P _ body, h, O =>
    ∀ F, s P (h.restrict O) = some F → UnannotConfinedAux s false body h F
  | _, .unannot body, h, O => UnannotConfinedAux s true body h O

/-- The footprint-confinement assumption on unannotated callees of a top-level program
run in a frame owning `O`: every read and write executed by an unannotated callee
targets an allocated byte of the frame (as attributed by the strategy `s`) in which the
callee runs. -/
def UnannotConfined (s : Strategy) (p : Prog) (h : Heap) (O : List Addr) : Prop :=
  UnannotConfinedAux s false p h O

end Toy.Monitor
