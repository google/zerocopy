-- Hybrid Verified Software (Wave 4): Deflate-style LZ77 cursor replay & Kraft checker.
-- Pure Init Lean 4 (no Mathlib, no omega, no bv_decide, no by_cases, zero sorry).

prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace HybridDeflateChecker

inductive LzToken where
  | lit (b : Nat)
  | matchTok (dist len : Nat)

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => listGet? xs k

def listTake {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, x :: xs => x :: listTake k xs

private theorem bool_and_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

private theorem nat_eq_of_beq_true : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg Nat.succ (nat_eq_of_beq_true (a := a) (b := b) h)

private theorem nat_le_of_ble_true {a b : Nat} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

private theorem nat_lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

private theorem listTake_len {α : Type} : ∀ (xs : List α), listTake xs.length xs = xs
  | [] => rfl
  | x :: xs => congrArg (x :: ·) (listTake_len xs)

private theorem listGet_lt_length {α : Type} : ∀ (xs : List α) (k : Nat) (x : α),
    listGet? xs k = some x → k < xs.length
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, k + 1, x, h => Nat.succ_lt_succ (listGet_lt_length xs k x h)

private theorem listTake_length_of_le {α : Type} :
    ∀ (xs : List α) (k : Nat), k ≤ xs.length → (listTake k xs).length = k
  | _, 0, _ => rfl
  | [], _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: xs, k + 1, h =>
    congrArg Nat.succ (listTake_length_of_le xs k (Nat.le_of_succ_le_succ h))

private theorem listTake_get_lt {α : Type} :
    ∀ (xs : List α) (k idx : Nat), idx < k →
      listGet? (listTake k xs) idx = listGet? xs idx
  | _, 0, _, h => nomatch h
  | [], _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: xs, k + 1, idx + 1, h =>
    listTake_get_lt xs k idx (Nat.lt_of_succ_lt_succ h)

private theorem listTake_append_get {α : Type} :
    ∀ (xs : List α) (k : Nat) (x : α),
      listGet? xs k = some x → listTake k xs ++ [x] = listTake (k + 1) xs
  | [], _, _, h => nomatch h
  | y :: _, 0, x, h => by
    injection h with hy
    rw [hy]
    rfl
  | y :: xs, k + 1, x, h => by
    dsimp [listTake, List.append]
    exact congrArg (y :: ·) (listTake_append_get xs k x h)

/-- Reference functional LZ77 decoder constructing output bytes sequentially. -/
def copyMatchStep (out : List Nat) (dist : Nat) : Nat → Option (List Nat)
  | 0 => some out
  | k + 1 =>
    match Nat.ble 1 dist && Nat.ble dist out.length with
    | false => none
    | true =>
      match listGet? out (out.length - dist) with
      | none => none
      | some b => copyMatchStep (out ++ [b]) dist k

def decodeLzAcc (out : List Nat) : List LzToken → Option (List Nat)
  | [] => some out
  | .lit b :: rest =>
    match Nat.blt b 256 with
    | false => none
    | true => decodeLzAcc (out ++ [b]) rest
  | .matchTok dist len :: rest =>
    match Nat.ble 1 len with
    | false => none
    | true =>
      match copyMatchStep out dist len with
      | none => none
      | some out' => decodeLzAcc out' rest

def decodeLzTokens (tokens : List LzToken) : Option (List Nat) :=
  decodeLzAcc [] tokens

/-- Zero-allocation cursor verifier checking `tokens` directly against `expected`. -/
def checkMatchCursor (expected : List Nat) (dist pos : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    match Nat.ble 1 dist && Nat.ble dist pos with
    | false => false
    | true =>
      match listGet? expected (pos - dist), listGet? expected pos with
      | some bPrev, some bCur =>
        Nat.beq bPrev bCur && checkMatchCursor expected dist (pos + 1) k
      | _, _ => false

def checkLzCursorAux (expected : List Nat) (pos : Nat) : List LzToken → Bool
  | [] => Nat.beq pos expected.length
  | .lit b :: rest =>
    match Nat.blt b 256 with
    | false => false
    | true =>
      match listGet? expected pos with
      | some eb => Nat.beq eb b && checkLzCursorAux expected (pos + 1) rest
      | none => false
  | .matchTok dist len :: rest =>
    Nat.ble 1 len &&
    checkMatchCursor expected dist pos len &&
    checkLzCursorAux expected (pos + len) rest

def checkLzReplay (expected : List Nat) (tokens : List LzToken) : Bool :=
  checkLzCursorAux expected 0 tokens

private theorem checkMatchCursor_sound (expected : List Nat) (dist : Nat) :
    ∀ (len pos : Nat),
      pos ≤ expected.length →
      checkMatchCursor expected dist pos len = true →
      copyMatchStep (listTake pos expected) dist len = some (listTake (pos + len) expected)
  | 0, pos, _, _ => rfl
  | k + 1, pos, hPosLe, hChk => by
    dsimp [checkMatchCursor] at hChk
    cases hBound : (Nat.ble 1 dist && Nat.ble dist pos) with
    | false => rw [hBound] at hChk; nomatch hChk
    | true =>
      rw [hBound] at hChk
      have hB := bool_and_split hBound
      have hDistPos : 1 ≤ dist := nat_le_of_ble_true hB.1
      have hDistLe : dist ≤ pos := nat_le_of_ble_true hB.2
      have hTakeLen : (listTake pos expected).length = pos :=
        listTake_length_of_le expected pos hPosLe
      cases hPrev : listGet? expected (pos - dist) with
      | none => rw [hPrev] at hChk; nomatch hChk
      | some bPrev =>
        rw [hPrev] at hChk
        cases hCur : listGet? expected pos with
        | none => rw [hCur] at hChk; nomatch hChk
        | some bCur =>
          rw [hCur] at hChk
          have hPair := bool_and_split hChk
          have hEqBytes := nat_eq_of_beq_true hPair.1
          have hCurLt : pos < expected.length := listGet_lt_length expected pos bCur hCur
          have hSubLt : pos - dist < pos := Nat.sub_lt (Nat.lt_of_lt_of_le hDistPos hDistLe) hDistPos
          have hTakeGet : listGet? (listTake pos expected) (pos - dist) = some bPrev := by
            rw [listTake_get_lt expected pos (pos - dist) hSubLt]
            exact hPrev
          dsimp [copyMatchStep]
          rw [hTakeLen, hBound, hTakeGet]
          dsimp
          have hAppend : listTake pos expected ++ [bPrev] = listTake (pos + 1) expected := by
            rw [hEqBytes]
            exact listTake_append_get expected pos bCur hCur
          rw [hAppend]
          have hNext := checkMatchCursor_sound expected dist k (pos + 1) hCurLt hPair.2
          rw [Nat.add_assoc, Nat.add_comm 1 k] at hNext
          exact hNext

private theorem checkLzCursorAux_sound (expected : List Nat) :
    ∀ (tokens : List LzToken) (pos : Nat),
      pos ≤ expected.length →
      checkLzCursorAux expected pos tokens = true →
      decodeLzAcc (listTake pos expected) tokens = some expected
  | [], pos, _, hChk => by
    dsimp [checkLzCursorAux] at hChk
    have hEq := nat_eq_of_beq_true hChk
    rw [hEq, listTake_len]
    rfl
  | .lit b :: rest, pos, _, hChk => by
    dsimp [checkLzCursorAux] at hChk
    cases hLt : Nat.blt b 256 with
    | false => rw [hLt] at hChk; nomatch hChk
    | true =>
      rw [hLt] at hChk
      cases hCur : listGet? expected pos with
      | none => rw [hCur] at hChk; nomatch hChk
      | some eb =>
        rw [hCur] at hChk
        have hPair := bool_and_split hChk
        have hEqB := nat_eq_of_beq_true hPair.1
        have hPosSuccLe : pos + 1 ≤ expected.length := listGet_lt_length expected pos eb hCur
        dsimp [decodeLzAcc]
        rw [hLt]
        dsimp
        have hApp : listTake pos expected ++ [b] = listTake (pos + 1) expected := by
          rw [← hEqB]
          exact listTake_append_get expected pos eb hCur
        rw [hApp]
        exact checkLzCursorAux_sound expected rest (pos + 1) hPosSuccLe hPair.2
  | .matchTok dist len :: rest, pos, hPosLe, hChk => by
    dsimp [checkLzCursorAux] at hChk
    have h1 := bool_and_split hChk
    have h2 := bool_and_split h1.1
    dsimp [decodeLzAcc]
    rw [h2.1]
    dsimp
    rw [checkMatchCursor_sound expected dist len pos hPosLe h2.2]
    dsimp
    -- Note: if checkMatchCursor returned true for len ≥ 1, then pos + len ≤ expected.length;
    -- however decodeLzAcc recurses cleanly when pos + len ≤ expected.length, proved next!
    have hLenBound : pos + len ≤ expected.length := by
      have hCursor := h2.2
      clear h1 h2 hChk
      induction len generalizing pos with
      | zero => exact hPosLe
      | succ k ih =>
        dsimp [checkMatchCursor] at hCursor
        cases hB : (Nat.ble 1 dist && Nat.ble dist pos) with
        | false => rw [hB] at hCursor; nomatch hCursor
        | true =>
          rw [hB] at hCursor
          cases hPrev : listGet? expected (pos - dist) with
          | none => rw [hPrev] at hCursor; nomatch hCursor
          | some _ =>
            rw [hPrev] at hCursor
            cases hCur : listGet? expected pos with
            | none => rw [hCur] at hCursor; nomatch hCursor
            | some bCur =>
              rw [hCur] at hCursor
              have hStep := bool_and_split hCursor
              have hP1 := listGet_lt_length expected pos bCur hCur
              have hRec := ih (pos + 1) hP1 hStep.2
              rw [Nat.add_assoc, Nat.add_comm 1 k] at hRec
              exact hRec
    exact checkLzCursorAux_sound expected rest (pos + len) hLenBound h1.2

/-- Soundness of the zero-allocation LZ77 cursor checker against the functional decoder. -/
theorem checkLzReplay_sound {expected : List Nat} {tokens : List LzToken}
    (hOk : checkLzReplay expected tokens = true) :
    decodeLzTokens tokens = some expected :=
  checkLzCursorAux_sound expected tokens 0 (Nat.zero_le _) hOk

/-! ## Canonical Huffman Kraft-Inequality & Bit-Length Checker -/

def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

def kraftWeight (maxBits len : Nat) : Nat :=
  match len with
  | 0 => 0
  | _ => pow2 (maxBits - len)

def kraftScaledSum (maxBits : Nat) : List Nat → Nat
  | [] => 0
  | l :: rest => kraftWeight maxBits l + kraftScaledSum maxBits rest

def allLe (cap : Nat) : List Nat → Bool
  | [] => true
  | l :: rest => Nat.ble l cap && allLe cap rest

private theorem allLe_sound (cap : Nat) :
    ∀ xs : List Nat, allLe cap xs = true → ∀ x, (∃ i, listGet? xs i = some x) → x ≤ cap
  | [], _, x, h => let ⟨_, hi⟩ := h; nomatch hi
  | y :: ys, hAll, x, ⟨i, hi⟩ => by
    have hPair := bool_and_split hAll
    cases i with
    | zero =>
      dsimp [listGet?] at hi
      injection hi with hy
      rw [← hy]
      exact nat_le_of_ble_true hPair.1
    | succ k =>
      exact allLe_sound cap ys hPair.2 x ⟨k, hi⟩

def checkKraftBounds (maxBits : Nat) (lengths : List Nat) : Bool :=
  allLe maxBits lengths && Nat.ble (kraftScaledSum maxBits lengths) (pow2 maxBits)

theorem checkKraftBounds_sound {maxBits : Nat} {lengths : List Nat}
    (hOk : checkKraftBounds maxBits lengths = true) :
    (∀ i l, listGet? lengths i = some l → l ≤ maxBits) ∧
      kraftScaledSum maxBits lengths ≤ pow2 maxBits := by
  dsimp [checkKraftBounds] at hOk
  have hPair := bool_and_split hOk
  exact ⟨fun i l hi => allLe_sound maxBits lengths hPair.1 l ⟨i, hi⟩,
    nat_le_of_ble_true hPair.2⟩

/-! ## Concrete Positive & Negative Canaries (`rfl`) -/

-- Input: [65, 66, 65, 66, 65, 66, 67] ("ABABABC")
-- Encoded with overlapping LZ77 match: lit 65, lit 66, match(dist=2, len=4), lit 67
def sampleBytes : List Nat := [65, 66, 65, 66, 65, 66, 67]
def sampleTokens : List LzToken := [.lit 65, .lit 66, .matchTok 2 4, .lit 67]
def sampleLengths : List Nat := [1, 2, 2] -- 2^14 + 2^13 + 2^13 = 32768 <= 32768 (maxBits=15)

theorem sampleLz_verified : decodeLzTokens sampleTokens = some sampleBytes :=
  checkLzReplay_sound rfl

theorem sampleKraft_verified :
    (∀ i l, listGet? sampleLengths i = some l → l ≤ 15) ∧
      kraftScaledSum 15 sampleLengths ≤ pow2 15 :=
  checkKraftBounds_sound rfl

-- Forged LZ77 corrupting byte 67 -> 68:
theorem forgedBadMatch_rejected :
    checkLzReplay sampleBytes [.lit 65, .lit 66, .matchTok 2 5] = false := rfl

-- Forged oversubscribed Kraft lengths [1, 1, 2] => 1/2 + 1/2 + 1/4 = 5/4 > 1:
theorem forgedKraftOversubscribed_rejected :
    checkKraftBounds 15 [1, 1, 2] = false := rfl

-- Forged Deflate length > 15:
theorem forgedMaxBitsExceeded_rejected :
    checkKraftBounds 15 [16] = false := rfl

#print axioms checkLzReplay_sound
#print axioms checkKraftBounds_sound
#print axioms sampleLz_verified

end HybridDeflateChecker
