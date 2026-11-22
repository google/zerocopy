/-!
# Kernel-Checked Formalization of `rustc_transmute` Byte-Level DFA Checking,
# Union-Transmute Truncation/Extension, `Def::has_safety_invariants` Pruning,
# and Reference `Freeze` Soundness (`rust-lang/rust#164247`)

Constructive, total Lean 4.34.1 kernel-checked mechanization over Core Lean only.
-/

namespace RustcTransmuteDfaAndRefSoundness

/-! ## 1. 257-Symbol Byte Alphabet (`Byte { start, end }` over `0..=256`) -/

/-- 257-symbol byte alphabet: `0..=255` are initialized bytes and `256` is `UNINIT`,
mirroring `compiler/rustc_transmute/src/layout/mod.rs` (`Byte::UNINIT = 256`). -/
abbrev ByteSym := Fin 257

/-- The distinguished uninitialized byte symbol `256`. -/
def uninitSym : ByteSym := ⟨256, by decide⟩

/-- Half-open byte range `[start, stop)` over `0..=256`, mirroring `layout::Byte`. -/
structure ByteRange where
  start : Nat
  stop : Nat
deriving DecidableEq, Repr

def ByteRange.contains (r : ByteRange) (b : ByteSym) : Bool :=
  decide (r.start ≤ b.val ∧ b.val < r.stop)

/-- `Byte::uninit()` in `rustc_transmute`: `[0, 257)` (`0..=255 | UNINIT`). -/
def ByteRange.uninit : ByteRange := ⟨0, 257⟩

/-- All initialized bytes `[0, 256)` (`0..=255`). -/
def ByteRange.anyInit : ByteRange := ⟨0, 256⟩

/-- `bool` byte range `[0, 2)` (`0x00..=0x01`). -/
def ByteRange.boolRange : ByteRange := ⟨0, 2⟩

/-- Singleton byte range `[v, v + 1)`. -/
def ByteRange.exact (v : Nat) : ByteRange := ⟨v, v + 1⟩

/-- Mirrors `Byte::contains_uninit`: `start <= 256 && 256 < end`. -/
def ByteRange.containsUninit (r : ByteRange) : Bool :=
  r.contains uninitSym

theorem uninit_contains_uninit : ByteRange.uninit.containsUninit = true := rfl

theorem anyInit_not_contains_uninit : ByteRange.anyInit.containsUninit = false := rfl

theorem uninit_contains_all (b : ByteSym) : ByteRange.uninit.contains b = true := by
  unfold ByteRange.contains ByteRange.uninit
  exact decide_eq_true ⟨Nat.zero_le b.val, b.isLt⟩

/-- Constructive enumeration of all 257 symbols in `Fin 257`. -/
def finListAux : (k : Nat) → (hk : k ≤ 257) → List ByteSym
  | 0, _ => []
  | k + 1, hk => ⟨k, hk⟩ :: finListAux k (Nat.le_of_succ_le hk)

def allBytes : List ByteSym := finListAux 257 (Nat.le_refl 257)

theorem mem_finListAux :
    ∀ (k : Nat) (hk : k ≤ 257) (b : ByteSym), b.val < k → b ∈ finListAux k hk
  | 0, _, b, hlt => False.elim (Nat.not_lt_zero b.val hlt)
  | k + 1, hk, b, hlt =>
    match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with
    | Or.inl heq =>
      have hb : b = ⟨k, hk⟩ := Fin.ext heq
      hb ▸ List.Mem.head _
    | Or.inr hlt' =>
      List.Mem.tail _ (mem_finListAux k (Nat.le_of_succ_le hk) b hlt')

theorem mem_allBytes (b : ByteSym) : b ∈ allBytes :=
  mem_finListAux 257 (Nat.le_refl 257) b b.isLt

/-! ## 2. Layout Trees and `Def::has_safety_invariants` Pruning -/

/-- Mirrors `layout::rustc::Def` (`compiler/rustc_transmute/src/layout/mod.rs`). -/
inductive DefKind where
  | adt
  | variant
  | field
  | primitive
deriving DecidableEq, Repr

/-- Mirrors `Def::has_safety_invariants(&self) -> bool { self != &Self::Primitive }`. -/
def DefKind.hasSafetyInvariants : DefKind → Bool
  | .primitive => false
  | .adt => true
  | .variant => true
  | .field => true

/-- Byte-level layout tree with zero-width `defNode` markers, mirroring `layout::Tree`. -/
inductive LayoutTree where
  | byte (r : ByteRange)
  | seq (elts : List LayoutTree)
  | alt (alts : List LayoutTree)
  | defNode (d : DefKind)
deriving Repr

def LayoutTree.unit : LayoutTree := .seq []
def LayoutTree.uninhabited : LayoutTree := .alt []

def LayoutTree.isUninhabited : LayoutTree → Bool
  | .alt [] => true
  | _ => false

def LayoutTree.thenTree (a b : LayoutTree) : LayoutTree :=
  match a, b with
  | .seq [], rhs => rhs
  | lhs, .seq [] => lhs
  | .seq xs, .seq ys => .seq (xs ++ ys)
  | .seq xs, rhs => .seq (xs ++ [rhs])
  | lhs, .seq ys => .seq (lhs :: ys)
  | lhs, rhs => .seq [lhs, rhs]

def LayoutTree.orTree (a b : LayoutTree) : LayoutTree :=
  match a, b with
  | .alt [], rhs => rhs
  | lhs, .alt [] => lhs
  | .alt xs, .alt ys => .alt (xs ++ ys)
  | .alt xs, rhs => .alt (xs ++ [rhs])
  | lhs, .alt ys => .alt (lhs :: ys)
  | lhs, rhs => .alt [lhs, rhs]

mutual
  /-- Mirrors `Tree::prune`: removes `defNode` annotations and rejects branches
  for which `pred d = true`. -/
  def LayoutTree.prune (pred : DefKind → Bool) : LayoutTree → LayoutTree
    | .byte r => .byte r
    | .defNode d => if pred d then LayoutTree.uninhabited else LayoutTree.unit
    | .seq elts => pruneSeq pred elts LayoutTree.unit
    | .alt alts => pruneAlt pred alts LayoutTree.uninhabited

  def pruneSeq (pred : DefKind → Bool) : List LayoutTree → LayoutTree → LayoutTree
    | [], acc => acc
    | x :: xs, acc =>
      let px := LayoutTree.prune pred x
      if px.isUninhabited then LayoutTree.uninhabited
      else pruneSeq pred xs (acc.thenTree px)

  def pruneAlt (pred : DefKind → Bool) : List LayoutTree → LayoutTree → LayoutTree
    | [], acc => acc
    | x :: xs, acc =>
      pruneAlt pred xs (acc.orTree (LayoutTree.prune pred x))
end

/-- `MaybeUninit<u8>` is a `#[repr(transparent)]` union ADT wrapped with `DefKind.adt`. -/
def maybeUninitU8Tree : LayoutTree :=
  .seq [.defNode .adt, .byte ByteRange.uninit]

theorem prune_safety_rejects_maybe_uninit :
    maybeUninitU8Tree.prune DefKind.hasSafetyInvariants = LayoutTree.uninhabited := rfl

theorem prune_assume_safety_retains_maybe_uninit :
    maybeUninitU8Tree.prune (fun _ => false) = .byte ByteRange.uninit := rfl

/-! ## 3. 257-Symbol Byte-Level DFA & Union-Transmute Semantics -/

/-- Deterministic finite automaton over the 257-symbol alphabet `Fin 257`. -/
structure ByteDfa where
  start : Nat
  accept : Nat
  step : Nat → ByteSym → Option Nat

/-- Computable word acceptance from an arbitrary state `s`. -/
def ByteDfa.acceptsFrom (d : ByteDfa) : Nat → List ByteSym → Bool
  | s, [] => s == d.accept
  | s, b :: bs =>
    match d.step s b with
    | none => false
    | some s' => d.acceptsFrom s' bs

/-- Language membership `w ∈ L(d)`. -/
def ByteDfa.accepts (d : ByteDfa) (w : List ByteSym) : Bool :=
  d.acceptsFrom d.start w

/-- Mirrors `Dfa::get_uninit_edge_dst`: checks whether `UNINIT` (`256`) transitions out of `s`. -/
def ByteDfa.getUninitEdgeDst (d : ByteDfa) (s : Nat) : Option Nat :=
  d.step s uninitSym

/-- Structural invariant of `rustc_transmute`'s `Dfa` (`dfa.rs:203-216`):
the accepting state has no outgoing transitions. -/
def AcceptHasNoOutEdges (d : ByteDfa) : Prop :=
  ∀ b : ByteSym, d.step d.accept b = none

/-- Every word accepted by `d` has exact byte length `n` (Invariant 1 of `layout::Tree`). -/
def FixedLen (d : ByteDfa) (n : Nat) : Prop :=
  ∀ w : List ByteSym, d.accepts w = true → w.length = n

/-- Multi-step reachability in a `ByteDfa`. -/
inductive Reachable (d : ByteDfa) : Nat → Nat → Prop where
  | refl (s : Nat) : Reachable d s s
  | step {s₁ s₂ s₃ : Nat} {b : ByteSym} :
      d.step s₁ b = some s₂ → Reachable d s₂ s₃ → Reachable d s₁ s₃

theorem Reachable.trans {d : ByteDfa} {s₁ s₂ s₃ : Nat}
    (h₁ : Reachable d s₁ s₂) (h₂ : Reachable d s₂ s₃) : Reachable d s₁ s₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hstep _ ih => exact Reachable.step hstep (ih h₂)

/-- Every state reachable from `d.start` can reach `d.accept` (no dead states;
guaranteed by `Dfa::from_tree` filtering uninhabited branches). -/
def LiveFrom (d : ByteDfa) : Prop :=
  ∀ s : Nat, Reachable d d.start s → ∃ w : List ByteSym, d.acceptsFrom s w = true

/-- Union-transmute compatibility between source byte sequence `wSrc` and destination DFA `dst`:
reading `dst` from `union { src: ManuallyDrop<Src>, dst: ManuallyDrop<Dst> }` either:
  (1) reads a prefix `wDst` of `wSrc` (prefix truncation when `size_of(Dst) <= size_of(Src)`), or
  (2) reads `wSrc` extended with `k` trailing `UNINIT` bytes (`size_of(Src) <= size_of(Dst)`). -/
def UnionTransmuteCompatFrom (dst : ByteDfa) (sDst : Nat) (wSrc : List ByteSym) : Prop :=
  ∃ wDst : List ByteSym,
    dst.acceptsFrom sDst wDst = true ∧
      ((∃ tail : List ByteSym, wSrc = wDst ++ tail) ∨
       (∃ k : Nat, wDst = wSrc ++ List.replicate k uninitSym))

def UnionTransmuteCompat (dst : ByteDfa) (wSrc : List ByteSym) : Prop :=
  UnionTransmuteCompatFrom dst dst.start wSrc

/-- Fuel-indexed recursive checker mirroring `MaybeTransmutableQuery::answer_impl`
(`compiler/rustc_transmute/src/maybe_transmutable/mod.rs:170-220`).
- `sDst == dst.accept` -> `true` (prefix truncation)
- `sSrc == src.accept` -> follow `dst.getUninitEdgeDst sDst` (trailing-uninit extension)
- otherwise: `assumeValidity = false` uses `Quantifier::ForAll`;
  `assumeValidity = true` uses `Quantifier::ThereExists`. -/
def dfaTransmute (src dst : ByteDfa) (assumeValidity : Bool) :
    Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, sSrc, sDst =>
    if sDst == dst.accept then
      true
    else if sSrc == src.accept then
      match dst.getUninitEdgeDst sDst with
      | some sDst' => dfaTransmute src dst assumeValidity fuel sSrc sDst'
      | none => false
    else
      if assumeValidity then
        allBytes.any (fun b =>
          match src.step sSrc b, dst.step sDst b with
          | some sSrc', some sDst' => dfaTransmute src dst true fuel sSrc' sDst'
          | _, _ => false)
      else
        allBytes.all (fun b =>
          match src.step sSrc b, dst.step sDst b with
          | none, _ => true
          | some _, none => false
          | some sSrc', some sDst' => dfaTransmute src dst false fuel sSrc' sDst')

/-! ### Helper Lemmas on Lists and Acceptance -/

theorem acceptsFrom_accept_eq_nil {d : ByteDfa} (hNoOut : AcceptHasNoOutEdges d) :
    ∀ w : List ByteSym, d.acceptsFrom d.accept w = true → w = []
  | [], _ => rfl
  | b :: bs, h => by
    unfold ByteDfa.acceptsFrom at h
    rw [hNoOut b] at h
    cases h

theorem list_all_true_of_mem {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, xs.all p = true → ∀ x, x ∈ xs → p x = true
  | [], _, _, hmem => nomatch hmem
  | y :: ys, hall, x, hmem => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    cases hmem with
    | head => exact hall.1
    | tail _ htail => exact list_all_true_of_mem hall.2 x htail

theorem list_any_true_iff_exists {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, xs.any p = true → ∃ x, x ∈ xs ∧ p x = true
  | [], hany => by cases hany
  | y :: ys, hany => by
    simp only [List.any_cons, Bool.or_eq_true] at hany
    cases hany with
    | inl hy => exact ⟨y, List.Mem.head _, hy⟩
    | inr hys =>
      let ⟨x, hmem, hx⟩ := list_any_true_iff_exists hys
      exact ⟨x, List.Mem.tail _ hmem, hx⟩

theorem eq_of_unionCompat_same_len {wSrc wDst : List ByteSym}
    (hlen : wSrc.length = wDst.length)
    (hrel : (∃ tail : List ByteSym, wSrc = wDst ++ tail) ∨
            (∃ k : Nat, wDst = wSrc ++ List.replicate k uninitSym)) :
    wSrc = wDst := by
  cases hrel with
  | inl hpref =>
    let ⟨tail, hEq⟩ := hpref
    have hl : wDst.length + 0 = wDst.length + tail.length := by
      calc wDst.length + 0 = wDst.length := Nat.add_zero _
        _ = wSrc.length := hlen.symm
        _ = (wDst ++ tail).length := congrArg List.length hEq
        _ = wDst.length + tail.length := List.length_append
    have ht0 : tail.length = 0 := (Nat.add_left_cancel hl).symm
    have htnil : tail = [] := List.eq_nil_of_length_eq_zero ht0
    rw [hEq, htnil, List.append_nil]
  | inr hext =>
    let ⟨k, hEq⟩ := hext
    have hl : wSrc.length + 0 = wSrc.length + k := by
      calc wSrc.length + 0 = wSrc.length := Nat.add_zero _
        _ = wDst.length := hlen
        _ = (wSrc ++ List.replicate k uninitSym).length := congrArg List.length hEq
        _ = wSrc.length + (List.replicate k uninitSym).length := List.length_append
        _ = wSrc.length + k := by rw [List.length_replicate]
    have hk0 : k = 0 := (Nat.add_left_cancel hl).symm
    rw [hEq, hk0, List.replicate_zero, List.append_nil]

/-! ### Theorem 1 & 2: DFA `ForAll` Union-Transmute Soundness and Language Inclusion -/

private theorem dfaTransmute_forall_sound_aux
    (src dst : ByteDfa)
    (hNoOut : AcceptHasNoOutEdges src) :
    ∀ (fuel sSrc sDst : Nat) (wSrc : List ByteSym),
      dfaTransmute src dst false fuel sSrc sDst = true →
      src.acceptsFrom sSrc wSrc = true →
      UnionTransmuteCompatFrom dst sDst wSrc
  | 0, _, _, _, hOk, _ => by cases hOk
  | fuel + 1, sSrc, sDst, wSrc, hOk, hSrc => by
    unfold dfaTransmute at hOk
    by_cases hDstAcc : (sDst == dst.accept) = true
    · have hDstEq : sDst = dst.accept := beq_iff_eq.mp hDstAcc
      refine ⟨[], ?_, Or.inl ⟨wSrc, rfl⟩⟩
      unfold ByteDfa.acceptsFrom
      exact beq_iff_eq.mpr hDstEq
    · rw [Bool.eq_false_iff.mpr hDstAcc] at hOk
      simp only [Bool.false_eq_true, ↓reduceIte] at hOk
      by_cases hSrcAcc : (sSrc == src.accept) = true
      · have hSrcEq : sSrc = src.accept := beq_iff_eq.mp hSrcAcc
        rw [hSrcAcc] at hOk
        simp only [↓reduceIte] at hOk
        have hwNil : wSrc = [] := acceptsFrom_accept_eq_nil hNoOut wSrc (hSrcEq ▸ hSrc)
        subst hwNil
        cases hUninit : dst.getUninitEdgeDst sDst with
        | none =>
          rw [hUninit] at hOk
          cases hOk
        | some sDst' =>
          rw [hUninit] at hOk
          have ih := dfaTransmute_forall_sound_aux src dst hNoOut fuel sSrc sDst' [] hOk hSrc
          let ⟨wDst', hAcc', hRel'⟩ := ih
          have hStepAcc : dst.acceptsFrom sDst (uninitSym :: wDst') = true := by
            unfold ByteDfa.acceptsFrom
            unfold ByteDfa.getUninitEdgeDst at hUninit
            rw [hUninit]
            exact hAcc'
          cases hRel' with
          | inl hpref =>
            let ⟨tail, hNilEq⟩ := hpref
            have hwDstNil : wDst' = [] := by
              cases wDst' with
              | nil => rfl
              | cons _ _ => cases hNilEq
            subst hwDstNil
            exact ⟨[uninitSym], hStepAcc, Or.inr ⟨1, rfl⟩⟩
          | inr hext =>
            let ⟨k, hRep⟩ := hext
            refine ⟨uninitSym :: wDst', hStepAcc, Or.inr ⟨k + 1, ?_⟩⟩
            rw [List.nil_append, List.replicate_succ, hRep, List.nil_append]
      · rw [Bool.eq_false_iff.mpr hSrcAcc] at hOk
        simp only [Bool.false_eq_true, ↓reduceIte] at hOk
        cases wSrc with
        | nil =>
          unfold ByteDfa.acceptsFrom at hSrc
          exact False.elim (hSrcAcc hSrc)
        | cons b bs =>
          unfold ByteDfa.acceptsFrom at hSrc
          cases hStepS : src.step sSrc b with
          | none =>
            rw [hStepS] at hSrc
            cases hSrc
          | some sSrc' =>
            rw [hStepS] at hSrc
            have hAllB := list_all_true_of_mem hOk b (mem_allBytes b)
            rw [hStepS] at hAllB
            cases hStepD : dst.step sDst b with
            | none =>
              rw [hStepD] at hAllB
              cases hAllB
            | some sDst' =>
              rw [hStepD] at hAllB
              have ih := dfaTransmute_forall_sound_aux src dst hNoOut fuel sSrc' sDst' bs hAllB hSrc
              let ⟨wDst', hAcc', hRel'⟩ := ih
              have hStepAcc : dst.acceptsFrom sDst (b :: wDst') = true := by
                unfold ByteDfa.acceptsFrom
                rw [hStepD]
                exact hAcc'
              cases hRel' with
              | inl hpref =>
                let ⟨tail, hEq⟩ := hpref
                exact ⟨b :: wDst', hStepAcc, Or.inl ⟨tail, by rw [hEq]; rfl⟩⟩
              | inr hext =>
                let ⟨k, hEq⟩ := hext
                exact ⟨b :: wDst', hStepAcc, Or.inr ⟨k, by rw [hEq]; rfl⟩⟩

/-- **Union-Transmute Prefix Truncation & Trailing-Uninit Soundness**:
If `dfaTransmute` accepts with `assumeValidity = false` (`Quantifier::ForAll`),
then every byte word accepted by `src` yields a valid `dst` word under either
prefix truncation (`size_of(Dst) <= size_of(Src)`) or trailing `UNINIT` extension
(`size_of(Src) <= size_of(Dst)`). -/
theorem union_transmute_trunc_and_pad_sound
    (src dst : ByteDfa) (fuel : Nat)
    (hNoOut : AcceptHasNoOutEdges src)
    (hOk : dfaTransmute src dst false fuel src.start dst.start = true)
    (wSrc : List ByteSym) (hSrc : src.accepts wSrc = true) :
    UnionTransmuteCompat dst wSrc :=
  dfaTransmute_forall_sound_aux src dst hNoOut fuel src.start dst.start wSrc hOk hSrc

/-- **DFA `ForAll` Language Inclusion (`assume.validity = false`)**:
For equal-size types (`FixedLen src n` and `FixedLen dst n`), `dfaTransmute` with
`assumeValidity = false` implies exact language inclusion `L(src) ⊆ L(dst)`. -/
theorem dfa_transmute_forall_implies_language_inclusion
    (src dst : ByteDfa) (n fuel : Nat)
    (hNoOut : AcceptHasNoOutEdges src)
    (hSrcLen : FixedLen src n)
    (hDstLen : FixedLen dst n)
    (hOk : dfaTransmute src dst false fuel src.start dst.start = true) :
    ∀ w : List ByteSym, src.accepts w = true → dst.accepts w = true := by
  intro w hSrc
  let ⟨wDst, hDst, hRel⟩ := union_transmute_trunc_and_pad_sound src dst fuel hNoOut hOk w hSrc
  have hlen : w.length = wDst.length := (hSrcLen w hSrc).trans (hDstLen wDst hDst).symm
  have hEq : w = wDst := eq_of_unionCompat_same_len hlen hRel
  rw [hEq]
  exact hDst

/-! ### Theorem 3: DFA `ThereExists` Non-Empty Intersection (`assume.validity = true`) -/

private theorem dfaTransmute_exists_witness_aux
    (src dst : ByteDfa)
    (hNoOut : AcceptHasNoOutEdges src)
    (hLive : LiveFrom src) :
    ∀ (fuel sSrc sDst : Nat),
      Reachable src src.start sSrc →
      dfaTransmute src dst true fuel sSrc sDst = true →
      ∃ wSrc : List ByteSym, src.acceptsFrom sSrc wSrc = true ∧ UnionTransmuteCompatFrom dst sDst wSrc
  | 0, _, _, _, hOk => by cases hOk
  | fuel + 1, sSrc, sDst, hReach, hOk => by
    unfold dfaTransmute at hOk
    by_cases hDstAcc : (sDst == dst.accept) = true
    · have hDstEq : sDst = dst.accept := beq_iff_eq.mp hDstAcc
      let ⟨wSrc, hSrc⟩ := hLive sSrc hReach
      refine ⟨wSrc, hSrc, [], ?_, Or.inl ⟨wSrc, rfl⟩⟩
      unfold ByteDfa.acceptsFrom
      exact beq_iff_eq.mpr hDstEq
    · rw [Bool.eq_false_iff.mpr hDstAcc] at hOk
      simp only [Bool.false_eq_true, ↓reduceIte] at hOk
      by_cases hSrcAcc : (sSrc == src.accept) = true
      · have hSrcEq : sSrc = src.accept := beq_iff_eq.mp hSrcAcc
        rw [hSrcAcc] at hOk
        simp only [↓reduceIte] at hOk
        cases hUninit : dst.getUninitEdgeDst sDst with
        | none =>
          rw [hUninit] at hOk
          cases hOk
        | some sDst' =>
          rw [hUninit] at hOk
          let ⟨wSrc, hSrc, wDst', hAcc', hRel'⟩ :=
            dfaTransmute_exists_witness_aux src dst hNoOut hLive fuel sSrc sDst' hReach hOk
          have hwNil : wSrc = [] := acceptsFrom_accept_eq_nil hNoOut wSrc (hSrcEq ▸ hSrc)
          subst hwNil
          have hStepAcc : dst.acceptsFrom sDst (uninitSym :: wDst') = true := by
            unfold ByteDfa.acceptsFrom
            unfold ByteDfa.getUninitEdgeDst at hUninit
            rw [hUninit]
            exact hAcc'
          cases hRel' with
          | inl hpref =>
            let ⟨tail, hNilEq⟩ := hpref
            have hwDstNil : wDst' = [] := by
              cases wDst' with
              | nil => rfl
              | cons _ _ => cases hNilEq
            subst hwDstNil
            exact ⟨[], hSrc, [uninitSym], hStepAcc, Or.inr ⟨1, rfl⟩⟩
          | inr hext =>
            let ⟨k, hRep⟩ := hext
            refine ⟨[], hSrc, uninitSym :: wDst', hStepAcc, Or.inr ⟨k + 1, ?_⟩⟩
            rw [List.nil_append, List.replicate_succ, hRep, List.nil_append]
      · rw [Bool.eq_false_iff.mpr hSrcAcc] at hOk
        simp only [Bool.false_eq_true, ↓reduceIte] at hOk
        let ⟨b, _, hMatch⟩ := list_any_true_iff_exists hOk
        cases hStepS : src.step sSrc b with
        | none =>
          rw [hStepS] at hMatch
          cases hMatch
        | some sSrc' =>
          rw [hStepS] at hMatch
          cases hStepD : dst.step sDst b with
          | none =>
            rw [hStepD] at hMatch
            cases hMatch
          | some sDst' =>
            rw [hStepD] at hMatch
            have hReach' : Reachable src src.start sSrc' :=
              hReach.trans (Reachable.step hStepS (Reachable.refl sSrc'))
            let ⟨wSrc', hSrc', wDst', hAcc', hRel'⟩ :=
              dfaTransmute_exists_witness_aux src dst hNoOut hLive fuel sSrc' sDst' hReach' hMatch
            have hSrcStep : src.acceptsFrom sSrc (b :: wSrc') = true := by
              unfold ByteDfa.acceptsFrom
              rw [hStepS]
              exact hSrc'
            have hDstStep : dst.acceptsFrom sDst (b :: wDst') = true := by
              unfold ByteDfa.acceptsFrom
              rw [hStepD]
              exact hAcc'
            cases hRel' with
            | inl hpref =>
              let ⟨tail, hEq⟩ := hpref
              exact ⟨b :: wSrc', hSrcStep, b :: wDst', hDstStep, Or.inl ⟨tail, by rw [hEq]; rfl⟩⟩
            | inr hext =>
              let ⟨k, hEq⟩ := hext
              exact ⟨b :: wSrc', hSrcStep, b :: wDst', hDstStep, Or.inr ⟨k, by rw [hEq]; rfl⟩⟩

/-- General union-transmute existential witness under `Assume::VALIDITY`. -/
theorem dfa_transmute_exists_union_witness
    (src dst : ByteDfa) (fuel : Nat)
    (hNoOut : AcceptHasNoOutEdges src)
    (hLive : LiveFrom src)
    (hOk : dfaTransmute src dst true fuel src.start dst.start = true) :
    ∃ wSrc : List ByteSym, src.accepts wSrc = true ∧ UnionTransmuteCompat dst wSrc :=
  dfaTransmute_exists_witness_aux src dst hNoOut hLive fuel src.start dst.start
    (Reachable.refl src.start) hOk

/-- **DFA `ThereExists` Non-Empty Intersection (`assume.validity = true`)**:
For equal-size types (`FixedLen src n` and `FixedLen dst n`), `dfaTransmute` with
`assumeValidity = true` (`Quantifier::ThereExists`) implies `L(src) ∩ L(dst) ≠ ∅`. -/
theorem dfa_transmute_exists_implies_nonempty_intersection
    (src dst : ByteDfa) (n fuel : Nat)
    (hNoOut : AcceptHasNoOutEdges src)
    (hLive : LiveFrom src)
    (hSrcLen : FixedLen src n)
    (hDstLen : FixedLen dst n)
    (hOk : dfaTransmute src dst true fuel src.start dst.start = true) :
    ∃ w : List ByteSym, src.accepts w = true ∧ dst.accepts w = true := by
  let ⟨wSrc, hSrc, wDst, hDst, hRel⟩ :=
    dfa_transmute_exists_union_witness src dst fuel hNoOut hLive hOk
  have hlen : wSrc.length = wDst.length := (hSrcLen wSrc hSrc).trans (hDstLen wDst hDst).symm
  have hEq : wSrc = wDst := eq_of_unionCompat_same_len hlen hRel
  rw [← hEq] at hDst
  exact ⟨wSrc, hSrc, hDst⟩

/-! ## 4. Concrete DFA Instances (Prefix Truncation, Trailing-Uninit Extension, Disjointness) -/

/-- Builds a straight-line byte-range DFA of length `ranges.length`:
state `i` transitions on `ranges[i]` to state `i + 1`, accepting at `ranges.length`. -/
def linearDfa (ranges : List ByteRange) : ByteDfa where
  start := 0
  accept := ranges.length
  step s b :=
    match ranges[s]? with
    | none => none
    | some r => if r.contains b then some (s + 1) else none

def u8Dfa : ByteDfa := linearDfa [ByteRange.anyInit]
def boolDfa : ByteDfa := linearDfa [ByteRange.boolRange]
def twoOnlyDfa : ByteDfa := linearDfa [ByteRange.exact 2]
def u16Dfa : ByteDfa := linearDfa [ByteRange.anyInit, ByteRange.anyInit]
def u32Dfa : ByteDfa := linearDfa [ByteRange.anyInit, ByteRange.anyInit, ByteRange.anyInit, ByteRange.anyInit]
def paddedAlign2Dfa : ByteDfa := linearDfa [ByteRange.anyInit, ByteRange.uninit]

theorem list_all_of_forall {α : Type} {p : α → Bool} :
    ∀ (xs : List α), (∀ x, p x = true) → xs.all p = true
  | [], _ => rfl
  | y :: ys, hall => by
    simp only [List.all_cons, hall y, Bool.true_and]
    exact list_all_of_forall ys hall

theorem union_transmute_u32_to_u8_prefix_trunc_accepted :
    dfaTransmute u32Dfa u8Dfa false 2 u32Dfa.start u8Dfa.start = true := by
  unfold dfaTransmute
  show allBytes.all (fun b =>
    match u32Dfa.step 0 b, u8Dfa.step 0 b with
    | none, _ => true
    | some _, none => false
    | some sSrc', some sDst' => dfaTransmute u32Dfa u8Dfa false 1 sSrc' sDst') = true
  apply list_all_of_forall
  intro b
  unfold u32Dfa u8Dfa linearDfa
  simp only [List.getElem?_cons_zero]
  cases ByteRange.anyInit.contains b <;> rfl

theorem union_transmute_u8_to_padded_align2_pad_ext_accepted :
    dfaTransmute u8Dfa paddedAlign2Dfa false 3 u8Dfa.start paddedAlign2Dfa.start = true := by
  unfold dfaTransmute
  show allBytes.all (fun b =>
    match u8Dfa.step 0 b, paddedAlign2Dfa.step 0 b with
    | none, _ => true
    | some _, none => false
    | some sSrc', some sDst' => dfaTransmute u8Dfa paddedAlign2Dfa false 2 sSrc' sDst') = true
  apply list_all_of_forall
  intro b
  unfold u8Dfa paddedAlign2Dfa linearDfa
  simp only [List.getElem?_cons_zero]
  cases ByteRange.anyInit.contains b
  · rfl
  · rfl

theorem union_transmute_u8_to_u16_rejected :
    dfaTransmute u8Dfa u16Dfa false 3 u8Dfa.start u16Dfa.start = false := by
  unfold dfaTransmute
  show allBytes.all (fun b =>
    match u8Dfa.step 0 b, u16Dfa.step 0 b with
    | none, _ => true
    | some _, none => false
    | some sSrc', some sDst' => dfaTransmute u8Dfa u16Dfa false 2 sSrc' sDst') = false
  cases hall : allBytes.all (fun b =>
    match u8Dfa.step 0 b, u16Dfa.step 0 b with
    | none, _ => true
    | some _, none => false
    | some sSrc', some sDst' => dfaTransmute u8Dfa u16Dfa false 2 sSrc' sDst') with
  | false => rfl
  | true =>
    have h0 := list_all_true_of_mem hall ⟨0, by decide⟩ (mem_allBytes ⟨0, by decide⟩)
    cases h0

/-! ### Counterexample 2: Disjoint Valid Sets Fail Even Under `Assume::VALIDITY` -/

theorem twoOnlyDfa_disjoint_boolDfa :
    ∀ w : List ByteSym, ¬ (twoOnlyDfa.accepts w = true ∧ boolDfa.accepts w = true) := by
  intro w h
  cases w with
  | nil =>
    have h1 := h.1
    cases h1
  | cons b bs =>
    cases bs with
    | nil =>
      have h1 := h.1
      have h2 := h.2
      unfold ByteDfa.accepts ByteDfa.acceptsFrom twoOnlyDfa linearDfa at h1
      unfold ByteDfa.accepts ByteDfa.acceptsFrom boolDfa linearDfa at h2
      simp only [List.getElem?_cons_zero] at h1 h2
      cases hc1 : ByteRange.exact 2 |>.contains b with
      | false =>
        rw [hc1] at h1
        cases h1
      | true =>
        cases hc2 : ByteRange.boolRange.contains b with
        | false =>
          rw [hc2] at h2
          cases h2
        | true =>
          unfold ByteRange.contains ByteRange.exact at hc1
          unfold ByteRange.contains ByteRange.boolRange at hc2
          have ⟨hge2, _⟩ := of_decide_eq_true hc1
          have ⟨_, hlt2⟩ := of_decide_eq_true hc2
          exact Nat.lt_irrefl 2 (Nat.lt_of_le_of_lt hge2 hlt2)
    | cons b2 bs2 =>
      have h1 := h.1
      unfold ByteDfa.accepts ByteDfa.acceptsFrom twoOnlyDfa linearDfa at h1
      simp only [List.getElem?_cons_zero] at h1
      cases hc1 : (ByteRange.exact 2).contains b with
      | false =>
        rw [hc1] at h1
        cases h1
      | true =>
        rw [hc1] at h1
        simp only [↓reduceIte] at h1
        cases h1

theorem twoOnly_to_bool_exists_false_all_fuel :
    ∀ fuel : Nat, dfaTransmute twoOnlyDfa boolDfa true fuel twoOnlyDfa.start boolDfa.start = false
  | 0 => rfl
  | fuel + 1 => by
    unfold dfaTransmute
    have h01 : (0 == 1) = false := rfl
    show (if (0 == 1) = true then true
          else if (0 == 1) = true then
            match boolDfa.getUninitEdgeDst 0 with
            | some sDst' => dfaTransmute twoOnlyDfa boolDfa true fuel 0 sDst'
            | none => false
          else
            allBytes.any (fun b =>
              match twoOnlyDfa.step 0 b, boolDfa.step 0 b with
              | some sSrc', some sDst' => dfaTransmute twoOnlyDfa boolDfa true fuel sSrc' sDst'
              | _, _ => false)) = false
    rw [h01]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hany : allBytes.any (fun b =>
        match twoOnlyDfa.step 0 b, boolDfa.step 0 b with
        | some sSrc', some sDst' => dfaTransmute twoOnlyDfa boolDfa true fuel sSrc' sDst'
        | _, _ => false) with
    | false => rfl
    | true =>
      let ⟨b, _, hb⟩ := list_any_true_iff_exists hany
      unfold twoOnlyDfa boolDfa linearDfa at hb
      simp only [List.getElem?_cons_zero] at hb
      cases hc1 : (ByteRange.exact 2).contains b with
      | false =>
        rw [hc1] at hb
        cases hb
      | true =>
        cases hc2 : ByteRange.boolRange.contains b with
        | false =>
          rw [hc1, hc2] at hb
          cases hb
        | true =>
          unfold ByteRange.contains ByteRange.exact at hc1
          unfold ByteRange.contains ByteRange.boolRange at hc2
          have ⟨hge2, _⟩ := of_decide_eq_true hc1
          have ⟨_, hlt2⟩ := of_decide_eq_true hc2
          exact False.elim (Nat.lt_irrefl 2 (Nat.lt_of_le_of_lt hge2 hlt2))

/-- **Counterexample 2 (`TwoOnly -> bool` under `Assume::VALIDITY`)**:
Because `Assume::VALIDITY` switches `Quantifier::ForAll` to `Quantifier::ThereExists`
(`L(Src) ∩ L(Dst) ≠ ∅`) rather than bypassing DFA checking, disjoint valid byte sets
(`{2}` vs `{0, 1}`) are rejected for every fuel bound and share no valid byte sequence. -/
theorem ce2_disjoint_valid_sets_fail_even_under_assume_validity :
    (∀ fuel : Nat,
      dfaTransmute twoOnlyDfa boolDfa true fuel twoOnlyDfa.start boolDfa.start = false) ∧
    (∀ w : List ByteSym, ¬ (twoOnlyDfa.accepts w = true ∧ boolDfa.accepts w = true)) :=
  ⟨twoOnly_to_bool_exists_false_all_fuel, twoOnlyDfa_disjoint_boolDfa⟩

/-! ### Counterexample 3: Unpruned Safety-Invariant ADT Is Unsound Without `Assume::SAFETY` -/

/-- `EvenU8`: single-byte ADT carrying a library safety invariant (`byte % 2 = 0`). -/
def evenU8Tree : LayoutTree :=
  .seq [.defNode .adt, .byte ByteRange.anyInit]

def evenU8SafetyInvariant (w : List ByteSym) : Prop :=
  match w with
  | [b] => b.val % 2 = 0
  | _ => False

def threeWord : List ByteSym := [⟨3, by decide⟩]

theorem u8_to_u8_dfa_accepted :
    dfaTransmute u8Dfa u8Dfa false 2 u8Dfa.start u8Dfa.start = true := by
  unfold dfaTransmute
  show allBytes.all (fun b =>
    match u8Dfa.step 0 b, u8Dfa.step 0 b with
    | none, _ => true
    | some _, none => false
    | some sSrc', some sDst' => dfaTransmute u8Dfa u8Dfa false 1 sSrc' sDst') = true
  apply list_all_of_forall
  intro b
  unfold u8Dfa linearDfa
  simp only [List.getElem?_cons_zero]
  cases ByteRange.anyInit.contains b <;> rfl

/-- **Counterexample 3 (Unpruned Safety-Invariant ADT)**:
1. With `Def::has_safety_invariants` pruning (`assume.safety = false`), `EvenU8` prunes to
   `LayoutTree.uninhabited` (`DstMayHaveSafetyInvariants`), rejecting `u8 -> EvenU8`.
2. Without pruning `DefKind.adt`, `u8 -> EvenU8` is accepted by the byte DFA (`u8Dfa -> u8Dfa`),
   yet the bit-valid `u8` word `[3]` violates `EvenU8`'s library safety invariant (`3 % 2 ≠ 0`). -/
theorem ce3_unpruned_safety_invariant_adt_unsound_without_assume_safety :
    evenU8Tree.prune DefKind.hasSafetyInvariants = LayoutTree.uninhabited ∧
    evenU8Tree.prune (fun _ => false) = .byte ByteRange.anyInit ∧
    dfaTransmute u8Dfa u8Dfa false 2 u8Dfa.start u8Dfa.start = true ∧
    u8Dfa.accepts threeWord = true ∧
    ¬ evenU8SafetyInvariant threeWord := by
  refine ⟨rfl, rfl, u8_to_u8_dfa_accepted, rfl, ?_⟩
  intro h
  unfold evenU8SafetyInvariant threeWord at h
  cases h

/-! ## 5. `Answer::or` Non-Boolean Retention Quirk -/

/-- Mirrors `rustc_type_ir::transmute::Answer` (`compiler/rustc_type_ir/src/transmute.rs:3-131`). -/
inductive RustcAnswer (C R : Type) where
  | yes
  | no (reason : R)
  | ifCond (cond : C)
deriving DecidableEq, Repr

/-- Exact upstream `Answer::or` behavior (`compiler/rustc_type_ir/src/transmute.rs:106-131`):
`(Yes, other) | (other, Yes) => other`, so combining `Yes` with `If(c)` retains `c`
instead of collapsing to `Yes`. -/
def RustcAnswer.orUpstream {C R : Type} (combineOr : C → C → C) (isGeneric : R → Bool) :
    RustcAnswer C R → RustcAnswer C R → RustcAnswer C R
  | .no r1, .no r2 => if isGeneric r1 then .no r2 else .no r1
  | .no _, .yes => .yes
  | .no _, .ifCond c => .ifCond c
  | .yes, .no _ => .yes
  | .ifCond c, .no _ => .ifCond c
  | .yes, other => other
  | other, .yes => other
  | .ifCond c1, .ifCond c2 => .ifCond (combineOr c1 c2)

/-- `Quantifier::ThereExists` fold (`maybe_transmutable/mod.rs:322-329`), breaking only on `.yes`. -/
def thereExistsFold {C R : Type} (combineOr : C → C → C) (isGeneric : R → Bool)
    (initReason : R) : List (RustcAnswer C R) → RustcAnswer C R :=
  go (.no initReason)
where
  go (acc : RustcAnswer C R) : List (RustcAnswer C R) → RustcAnswer C R
    | [] => acc
    | x :: xs =>
      match RustcAnswer.orUpstream combineOr isGeneric acc x with
      | .yes => .yes
      | next => go next xs

/-- Upstream `Answer::or` fails Boolean absorption (`If(c) ∨ Yes = If(c) ≠ Yes`), causing
`Quantifier::ThereExists` to depend on branch order (`[If(c), Yes]` retains `If(c)` while
`[Yes, If(c)]` short-circuits to `Yes`). -/
theorem upstream_answer_or_order_asymmetry {C R : Type}
    (combineOr : C → C → C) (isGeneric : R → Bool) (r0 : R) (c : C) :
    thereExistsFold combineOr isGeneric r0 [.ifCond c, .yes] = .ifCond c ∧
    thereExistsFold combineOr isGeneric r0 [.yes, .ifCond c] = .yes :=
  ⟨rfl, rfl⟩

/-! ## 6. Reference Transmutability Conditions & Operational Read-Only Aliasing Model -/

/-- Reference layout and freeze attributes at a DFA reference transition. -/
structure RefSpec where
  isMut : Bool
  isFreeze : Bool
  align : Nat
  size : Nat
deriving DecidableEq, Repr

/-- Mirrors `core::mem::Assume`. -/
structure AssumeOpts where
  alignment : Bool
  lifetimes : Bool
  safety : Bool
  validity : Bool
deriving DecidableEq, Repr

def AssumeOpts.nothing : AssumeOpts := ⟨false, false, false, false⟩

/-- Obligations emitted by `maybe_transmutable` for a single `(src_ref, dst_ref)` pair. -/
structure RefObligations where
  allowed : Bool
  reqForwardTransmute : Bool
  reqReverseTransmute : Bool
  reqOutlives : Bool
  reqDstFreeze : Bool
  reqSrcFreeze : Bool
deriving DecidableEq, Repr

/-- **Upstream buggy obligation generator** (`compiler/rustc_transmute/src/maybe_transmutable/mod.rs:244-289`,
pinned at `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):
When `!dst.isMut`, emits `Condition::Immutable { ty: dst.referent }` (`reqDstFreeze = true`),
but **omits** `Condition::Immutable { ty: src.referent }` (`reqSrcFreeze = false`), permitting
`&Cell<T> -> &T` under `Assume::NOTHING` (`rust-lang/rust#164247`). -/
def refConditionsUpstream (assume : AssumeOpts) (src dst : RefSpec) : RefObligations :=
  let guardOk :=
    !(!src.isMut && dst.isMut) &&
    (assume.alignment || decide (dst.align ≤ src.align)) &&
    decide (dst.size ≤ src.size)
  { allowed := guardOk
    reqForwardTransmute := true
    reqReverseTransmute := dst.isMut
    reqOutlives := !assume.lifetimes
    reqDstFreeze := !dst.isMut
    reqSrcFreeze := false }

/-- **Repaired obligation generator**:
Identical to upstream except that when transmuting a shared reference to a shared reference
(`!src.isMut && !dst.isMut`), it ALSO requires `Condition::Immutable { ty: src.referent }`
(`reqSrcFreeze = !src.isMut && !dst.isMut`). Consuming a unique `&mut Cell<T>` into `&T`
leaves no live interior-mutable alias and remains permitted. -/
def refConditionsRepaired (assume : AssumeOpts) (src dst : RefSpec) : RefObligations :=
  let guardOk :=
    !(!src.isMut && dst.isMut) &&
    (assume.alignment || decide (dst.align ≤ src.align)) &&
    decide (dst.size ≤ src.size)
  { allowed := guardOk
    reqForwardTransmute := true
    reqReverseTransmute := dst.isMut
    reqOutlives := !assume.lifetimes
    reqDstFreeze := !dst.isMut
    reqSrcFreeze := !src.isMut && !dst.isMut }

/-- Evaluates whether all obligations emitted by `ob` are discharged. -/
def refDischarged (ob : RefObligations) (src dst : RefSpec)
    (fwdOk revOk outlivesOk : Bool) : Bool :=
  ob.allowed &&
  (!ob.reqForwardTransmute || fwdOk) &&
  (!ob.reqReverseTransmute || revOk) &&
  (!ob.reqOutlives || outlivesOk) &&
  (!ob.reqDstFreeze || dst.isFreeze) &&
  (!ob.reqSrcFreeze || src.isFreeze)

/-! ### Operational Aliasing & Read-Only Tag Model (Stacked/Tree Borrows & LLVM `readonly`) -/

/-- Access capability of a handle after by-value reference transmutation:
- `consumed`: unique `&mut Src` moved into `TransmuteFrom::transmute`, leaving no live source alias;
- `sharedRO`: `Copy` shared `&T` with `T: Freeze` (Miri `SharedReadOnly` / `Frozen`, LLVM `readonly`);
- `sharedRW`: `Copy` shared `&T` with `!T: Freeze` (`Cell`/`UnsafeCell`, Miri `SharedReadWrite` / `Cell`);
- `uniqueRW`: unique `&mut Dst` (Miri `Unique` / `Active`). -/
inductive HandleCap where
  | consumed
  | sharedRO
  | sharedRW
  | uniqueRW
deriving DecidableEq, Repr

def srcPostTransmuteCap (src : RefSpec) : HandleCap :=
  if src.isMut then .consumed
  else if src.isFreeze then .sharedRO
  else .sharedRW

def dstPostTransmuteCap (dst : RefSpec) : HandleCap :=
  if dst.isMut then .uniqueRW
  else if dst.isFreeze then .sharedRO
  else .sharedRW

/-- Small-step memory + aliasing tag state for the transmuted referent byte. -/
structure AliasState where
  srcCap : HandleCap
  dstCap : HandleCap
  memVal : Nat
  initVal : Nat
  dstReadOnlyInvalidated : Bool
  srcReadOnlyInvalidated : Bool
  ubOccurred : Bool
deriving DecidableEq, Repr

def initAliasState (src dst : RefSpec) (v0 : Nat) : AliasState :=
  { srcCap := srcPostTransmuteCap src
    dstCap := dstPostTransmuteCap dst
    memVal := v0
    initVal := v0
    dstReadOnlyInvalidated := false
    srcReadOnlyInvalidated := false
    ubOccurred := false }

/-- Operations permitted by safe Rust code on the surviving `(src, dst)` handles. -/
inductive AliasStep where
  | readDst
  | readSrc
  | writeSrc (v : Nat)
  | writeDst (v : Nat)
deriving DecidableEq, Repr

/-- Whether an `AliasStep` is well-typed in safe Rust given `(srcCap, dstCap)`. -/
def stepPermitted (st : AliasState) : AliasStep → Bool
  | .readDst => true
  | .readSrc => st.srcCap != .consumed
  | .writeSrc _ => st.srcCap == .sharedRW
  | .writeDst _ => st.dstCap == .uniqueRW || st.dstCap == .sharedRW

/-- Operational transition:
- Writing through `src` (`Cell::set`) invalidates a live `.sharedRO` `dst` tag;
- Writing through `dst` invalidates a live `.sharedRO` `src` tag;
- Reading through a `.sharedRO` handle whose tag was invalidated triggers immediate UB. -/
def execAliasStep (st : AliasState) : AliasStep → AliasState
  | .readDst =>
    if st.dstCap == .sharedRO && st.dstReadOnlyInvalidated then
      { st with ubOccurred := true }
    else st
  | .readSrc =>
    if st.srcCap == .sharedRO && st.srcReadOnlyInvalidated then
      { st with ubOccurred := true }
    else st
  | .writeSrc v =>
    if st.srcCap == .sharedRW then
      { st with
          memVal := v
          dstReadOnlyInvalidated := st.dstReadOnlyInvalidated || (st.dstCap == .sharedRO) }
    else st
  | .writeDst v =>
    if st.dstCap == .uniqueRW || st.dstCap == .sharedRW then
      { st with
          memVal := v
          srcReadOnlyInvalidated := st.srcReadOnlyInvalidated || (st.srcCap == .sharedRO) }
    else st

def execAliasTrace (st : AliasState) : List AliasStep → AliasState
  | [] => st
  | s :: ss => execAliasTrace (execAliasStep st s) ss

/-- All steps in a trace are permitted by safe Rust typing. -/
def TracePermitted (st : AliasState) : List AliasStep → Prop
  | [] => True
  | s :: ss => stepPermitted st s = true ∧ TracePermitted (execAliasStep st s) ss

/-- **Soundness invariant preserved across traces**:
No read-only tag is invalidated, no aliasing UB occurs, and whenever `dstCap = .sharedRO`,
memory never diverges from `initVal` (justifying LLVM `readonly` caching). -/
def ReadOnlyInvariant (st : AliasState) : Prop :=
  st.ubOccurred = false ∧
  st.dstReadOnlyInvalidated = false ∧
  st.srcReadOnlyInvalidated = false ∧
  (st.dstCap = .sharedRO → st.memVal = st.initVal)

private theorem repaired_discharged_implies_caps_safe
    (assume : AssumeOpts) (src dst : RefSpec) (fwdOk revOk outlivesOk : Bool)
    (hOk : refDischarged (refConditionsRepaired assume src dst) src dst fwdOk revOk outlivesOk = true) :
    srcPostTransmuteCap src ≠ .sharedRW ∧
    dstPostTransmuteCap dst ≠ .sharedRW ∧
    (dstPostTransmuteCap dst = .uniqueRW → srcPostTransmuteCap src = .consumed) := by
  unfold refDischarged refConditionsRepaired at hOk
  cases hsm : src.isMut <;> cases hdm : dst.isMut <;>
    cases hsf : src.isFreeze <;> cases hdf : dst.isFreeze <;>
    simp_all [srcPostTransmuteCap, dstPostTransmuteCap]

private theorem execAliasStep_preserves_ro
    (st : AliasState) (step : AliasStep)
    (hNoSrcRW : st.srcCap ≠ .sharedRW)
    (hNoDstRW : st.dstCap ≠ .sharedRW)
    (hMutExclusive : st.dstCap = .uniqueRW → st.srcCap = .consumed)
    (hInv : ReadOnlyInvariant st) :
    ReadOnlyInvariant (execAliasStep st step) ∧
    (execAliasStep st step).srcCap = st.srcCap ∧
    (execAliasStep st step).dstCap = st.dstCap := by
  rcases st with ⟨srcCap, dstCap, memVal, initVal, dstInv, srcInv, ub⟩
  rcases hInv with ⟨hUb, hDstInv, hSrcInv, hRoVal⟩
  subst hUb; subst hDstInv; subst hSrcInv
  cases step with
  | readDst =>
    cases dstCap <;> exact ⟨⟨rfl, rfl, rfl, hRoVal⟩, rfl, rfl⟩
  | readSrc =>
    cases srcCap <;> exact ⟨⟨rfl, rfl, rfl, hRoVal⟩, rfl, rfl⟩
  | writeSrc v =>
    cases srcCap with
    | consumed => exact ⟨⟨rfl, rfl, rfl, hRoVal⟩, rfl, rfl⟩
    | sharedRO => exact ⟨⟨rfl, rfl, rfl, hRoVal⟩, rfl, rfl⟩
    | uniqueRW => exact ⟨⟨rfl, rfl, rfl, hRoVal⟩, rfl, rfl⟩
    | sharedRW => exact False.elim (hNoSrcRW rfl)
  | writeDst v =>
    cases dstCap with
    | consumed => exact ⟨⟨rfl, rfl, rfl, hRoVal⟩, rfl, rfl⟩
    | sharedRO => exact ⟨⟨rfl, rfl, rfl, hRoVal⟩, rfl, rfl⟩
    | sharedRW => exact False.elim (hNoDstRW rfl)
    | uniqueRW =>
      have hsc : srcCap = .consumed := hMutExclusive rfl
      subst hsc
      exact ⟨⟨rfl, rfl, rfl, fun h => nomatch h⟩, rfl, rfl⟩

private theorem execAliasTrace_preserves_ro
    (st : AliasState) (tr : List AliasStep)
    (hNoSrcRW : st.srcCap ≠ .sharedRW)
    (hNoDstRW : st.dstCap ≠ .sharedRW)
    (hMutExclusive : st.dstCap = .uniqueRW → st.srcCap = .consumed)
    (hInv : ReadOnlyInvariant st) :
    ReadOnlyInvariant (execAliasTrace st tr) := by
  induction tr generalizing st with
  | nil => exact hInv
  | cons s ss ih =>
    have ⟨hInv', hSrcEq, hDstEq⟩ :=
      execAliasStep_preserves_ro st s hNoSrcRW hNoDstRW hMutExclusive hInv
    exact ih (execAliasStep st s) (hSrcEq ▸ hNoSrcRW) (hDstEq ▸ hNoDstRW)
      (fun h => hSrcEq ▸ hMutExclusive (hDstEq ▸ h)) hInv'

/-- **Theorem 4 (Repaired Reference `Freeze` Rule Soundness)**:
Whenever the repaired obligation generator (`reqSrcFreeze := !src.isMut && !dst.isMut`,
`reqDstFreeze := !dst.isMut`) is discharged for `(assume, src, dst)`, every safe Rust
execution trace `tr` starting from `initAliasState src dst v0` preserves
`ReadOnlyInvariant`: no `SharedReadOnly`/`Frozen` tag is invalidated, zero aliasing UB
occurs, and any shared read-only destination `&Dst` always observes the exact initial value `v0`. -/
theorem repaired_ref_transmute_preserves_readonly_invariant
    (assume : AssumeOpts) (src dst : RefSpec) (fwdOk revOk outlivesOk : Bool)
    (v0 : Nat) (tr : List AliasStep)
    (hOk : refDischarged (refConditionsRepaired assume src dst) src dst fwdOk revOk outlivesOk = true) :
    ReadOnlyInvariant (execAliasTrace (initAliasState src dst v0) tr) := by
  have ⟨hNoSrcRW, hNoDstRW, hMutExcl⟩ :=
    repaired_discharged_implies_caps_safe assume src dst fwdOk revOk outlivesOk hOk
  exact execAliasTrace_preserves_ro (initAliasState src dst v0) tr
    hNoSrcRW hNoDstRW hMutExcl ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-! ### Positive Controls for the Repaired Rule -/

def refCellU8 : RefSpec := { isMut := false, isFreeze := false, align := 1, size := 1 }
def refU8 : RefSpec := { isMut := false, isFreeze := true, align := 1, size := 1 }
def refMutCellU8 : RefSpec := { isMut := true, isFreeze := false, align := 1, size := 1 }
def refMutU8 : RefSpec := { isMut := true, isFreeze := true, align := 1, size := 1 }

/-- Consuming unique `&mut Cell<u8>` into `&u8` leaves `srcCap = .consumed` and stays sound. -/
theorem repaired_ref_allows_mut_cell_to_shared_ro :
    refDischarged (refConditionsRepaired AssumeOpts.nothing refMutCellU8 refU8)
      refMutCellU8 refU8 true false true = true := rfl

/-- Shared-to-mutable (`&u8 -> &mut u8`) is rejected (`DstIsMoreUnique`). -/
theorem repaired_ref_rejects_shared_to_mut :
    refDischarged (refConditionsRepaired AssumeOpts.nothing refU8 refMutU8)
      refU8 refMutU8 true true true = false := rfl

/-- Mutable-to-mutable (`&mut u32 -> &mut u8`) requires reverse transmutability (`revOk = true`). -/
theorem repaired_ref_requires_reverse_for_mut_to_mut :
    refDischarged (refConditionsRepaired AssumeOpts.nothing refMutU8 refMutU8)
      refMutU8 refMutU8 true false true = false := rfl

/-! ### Counterexample 1: Live Upstream Bug `rust-lang/rust#164247` (`&Cell<u8> -> &u8`) -/

/-- Exact 3-step trace of `rust-lang/rust#164247`:
`before = *ro` (7), `cell.set(99)`, `after = *ro` (UB; `-O0` reads 99, `-O2` reads stale 7). -/
def issue164247Trace : List AliasStep :=
  [.readDst, .writeSrc 99, .readDst]

/-- **Counterexample 1 (`rust-lang/rust#164247`)**:
1. Upstream `refConditionsUpstream` accepts `&Cell<u8> -> &u8` under `Assume::NOTHING`.
2. Repaired `refConditionsRepaired` rejects `&Cell<u8> -> &u8` under `Assume::NOTHING`.
3. The 3-step safe-Rust trace `[readDst, writeSrc 99, readDst]` starting from `v0 = 7`
   is well-typed (`TracePermitted`), invalidates `ro`'s `SharedReadOnly`/`Frozen` tag,
   triggers immediate aliasing UB (`ubOccurred = true`), and diverges between actual
   memory (`memVal = 99`, matching `-O0`) and initial cached value (`initVal = 7`, matching `-O2`). -/
theorem ce1_upstream_missing_src_freeze_allows_cell_to_readonly_ref_ub :
    refDischarged (refConditionsUpstream AssumeOpts.nothing refCellU8 refU8)
      refCellU8 refU8 true false true = true ∧
    refDischarged (refConditionsRepaired AssumeOpts.nothing refCellU8 refU8)
      refCellU8 refU8 true false true = false ∧
    TracePermitted (initAliasState refCellU8 refU8 7) issue164247Trace ∧
    (execAliasTrace (initAliasState refCellU8 refU8 7) issue164247Trace).ubOccurred = true ∧
    (execAliasTrace (initAliasState refCellU8 refU8 7) issue164247Trace).memVal = 99 ∧
    (execAliasTrace (initAliasState refCellU8 refU8 7) issue164247Trace).initVal = 7 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, rfl, trivial⟩

end RustcTransmuteDfaAndRefSoundness
