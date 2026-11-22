prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Option.Basic

namespace SqlRewriteAndIteratorTypestate

/-!
# 3VL + Error-Aware Inner-Join Filter Mirroring, 4-Branch `LIMIT`/`OFFSET` Folding,
# and `googlesql::EvaluatorTableIterator` Lifecycle Typestate
-/

/-! ## 1. 3VL + Error-Aware Join Filter Mirroring -/

inductive PredEval where
  | valTrue
  | valFalse
  | valNull
  | runtimeErr

def PredEval.isKeep : PredEval → Bool
  | .valTrue => true
  | _        => false

noncomputable def evalFilterTable {K : Type} (p : K → PredEval) : List K → Option (List K)
  | [] => some []
  | x :: xs =>
    match p x with
    | .runtimeErr => none
    | r =>
      match evalFilterTable p xs with
      | none      => none
      | some rest => some (match r.isKeep with | true => x :: rest | false => rest)

def evalInnerJoin {K : Type} (eqK : K → K → Bool) (left right : List K) : List (K × K) :=
  left.foldr
    (fun l acc =>
      (right.foldr (fun r inner => match eqK l r with | true => (l, r) :: inner | false => inner) []) ++ acc)
    []

noncomputable def joinFilterLeftOnly {K : Type} (eqK : K → K → Bool) (p : K → PredEval) (left right : List K) : Option (List (K × K)) :=
  match evalFilterTable p left with
  | none    => none
  | some fl => some (evalInnerJoin eqK fl right)

noncomputable def joinFilterMirrored {K : Type} (eqK : K → K → Bool) (p : K → PredEval) (left right : List K) : Option (List (K × K)) :=
  match evalFilterTable p left, evalFilterTable p right with
  | some fl, some fr => some (evalInnerJoin eqK fl fr)
  | _, _             => none

inductive FloatKey where
  | negZero
  | posZero
  | posOne

def floatJoinEq : FloatKey → FloatKey → Bool
  | .negZero, .negZero => true
  | .negZero, .posZero => true
  | .posZero, .negZero => true
  | .posZero, .posZero => true
  | .posOne,  .posOne  => true
  | _, _               => false

def recipNegPred : FloatKey → PredEval
  | .negZero => .valTrue
  | .posZero => .valFalse
  | .posOne  => .valFalse

theorem naiveJoinMirror_drops_signedZero_match :
    joinFilterLeftOnly floatJoinEq recipNegPred [.negZero] [.posZero] = some [(.negZero, .posZero)] ∧
    joinFilterMirrored floatJoinEq recipNegPred [.negZero] [.posZero] = some [] :=
  ⟨rfl, rfl⟩

def fallibleDivPosPred (k : Nat) : PredEval :=
  match k with
  | 0 => .runtimeErr
  | _ => .valTrue

theorem fallibleJoinMirror_introduces_spurious_error_on_unmatched_rhs :
    (∀ x y, Nat.beq x y = true → fallibleDivPosPred x = fallibleDivPosPred y) ∧
    joinFilterLeftOnly Nat.beq fallibleDivPosPred [] [0] = some [] ∧
    joinFilterMirrored Nat.beq fallibleDivPosPred [] [0] = none := by
  refine ⟨?_, rfl, rfl⟩
  intro x y hBeq
  have hEq : x = y := Nat.eq_of_beq_eq_true hBeq
  rw [hEq]

private theorem evalFilterTable_total_of_infallible {K : Type}
    (p : K → PredEval) (hNoErr : ∀ r, (p r = .runtimeErr) → False) :
    ∀ (rs : List K), ∃ fr, evalFilterTable p rs = some fr
  | [] => ⟨[], rfl⟩
  | r :: rs => by
    dsimp only [evalFilterTable]
    cases hPr : p r
    · cases evalFilterTable_total_of_infallible p hNoErr rs with | intro fr hFr =>
      rw [hFr]; exact ⟨r :: fr, rfl⟩
    · cases evalFilterTable_total_of_infallible p hNoErr rs with | intro fr hFr =>
      rw [hFr]; exact ⟨fr, rfl⟩
    · cases evalFilterTable_total_of_infallible p hNoErr rs with | intro fr hFr =>
      rw [hFr]; exact ⟨fr, rfl⟩
    · exfalso; exact hNoErr r hPr

private theorem foldr_inner_mirrored_3vl {K : Type}
    (eqK : K → K → Bool) (p : K → PredEval)
    (hCong : ∀ x y, eqK x y = true → (p x).isKeep = (p y).isKeep)
    (l : K) (hKeepL : (p l).isKeep = true) :
    ∀ (right fr : List K),
      evalFilterTable p right = some fr →
      fr.foldr (fun r inner => match eqK l r with | true => (l, r) :: inner | false => inner) [] =
      right.foldr (fun r inner => match eqK l r with | true => (l, r) :: inner | false => inner) []
  | [], _, hF => by
    dsimp only [evalFilterTable] at hF
    injection hF with hEq
    rw [← hEq]
  | r :: rs, fr, hF => by
    dsimp only [evalFilterTable] at hF
    revert hF
    cases hPr : p r
    · cases hRest : evalFilterTable p rs
      · intro hFalse; nomatch hFalse
      · rename_i restFr
        intro hSome
        injection hSome with hFrEq
        rw [← hFrEq]
        dsimp only [PredEval.isKeep, List.foldr]
        rw [foldr_inner_mirrored_3vl eqK p hCong l hKeepL rs restFr hRest]
    · cases hRest : evalFilterTable p rs
      · intro hFalse; nomatch hFalse
      · rename_i restFr
        intro hSome
        injection hSome with hFrEq
        rw [← hFrEq]
        dsimp only [PredEval.isKeep, List.foldr]
        cases hEq : eqK l r
        · exact foldr_inner_mirrored_3vl eqK p hCong l hKeepL rs restFr hRest
        · have hC := hCong l r hEq
          rw [hKeepL, hPr] at hC
          nomatch hC
    · cases hRest : evalFilterTable p rs
      · intro hFalse; nomatch hFalse
      · rename_i restFr
        intro hSome
        injection hSome with hFrEq
        rw [← hFrEq]
        dsimp only [PredEval.isKeep, List.foldr]
        cases hEq : eqK l r
        · exact foldr_inner_mirrored_3vl eqK p hCong l hKeepL rs restFr hRest
        · have hC := hCong l r hEq
          rw [hKeepL, hPr] at hC
          nomatch hC
    · intro hFalse; nomatch hFalse

private theorem evalInnerJoin_mirrored_aux {K : Type}
    (eqK : K → K → Bool) (p : K → PredEval)
    (hCong : ∀ x y, eqK x y = true → (p x).isKeep = (p y).isKeep)
    (right fr : List K) (hFr : evalFilterTable p right = some fr) :
    ∀ (left fl : List K),
      evalFilterTable p left = some fl →
      evalInnerJoin eqK fl fr = evalInnerJoin eqK fl right
  | [], _, hFl => by
    dsimp only [evalFilterTable] at hFl
    injection hFl with hEq
    rw [← hEq]; rfl
  | l :: ls, fl, hFl => by
    dsimp only [evalFilterTable] at hFl
    revert hFl
    cases hPl : p l
    · cases hRestL : evalFilterTable p ls
      · intro hFalse; nomatch hFalse
      · rename_i restFl
        intro hSome
        injection hSome with hEqFl
        rw [← hEqFl]
        dsimp only [PredEval.isKeep, evalInnerJoin, List.foldr]
        have hKeepL : (p l).isKeep = true := by rw [hPl]; rfl
        rw [foldr_inner_mirrored_3vl eqK p hCong l hKeepL right fr hFr]
        have ih := evalInnerJoin_mirrored_aux eqK p hCong right fr hFr ls restFl hRestL
        dsimp only [evalInnerJoin] at ih
        rw [ih]
    · cases hRestL : evalFilterTable p ls
      · intro hFalse; nomatch hFalse
      · rename_i restFl
        intro hSome; injection hSome with hEqFl; rw [← hEqFl]
        exact evalInnerJoin_mirrored_aux eqK p hCong right fr hFr ls restFl hRestL
    · cases hRestL : evalFilterTable p ls
      · intro hFalse; nomatch hFalse
      · rename_i restFl
        intro hSome; injection hSome with hEqFl; rw [← hEqFl]
        exact evalInnerJoin_mirrored_aux eqK p hCong right fr hFr ls restFl hRestL
    · intro hFalse; nomatch hFalse

theorem joinFilterMirror_exact_of_infallible_and_congruent {K : Type}
    (eqK : K → K → Bool) (p : K → PredEval)
    (hNoErrR : ∀ r, (p r = .runtimeErr) → False)
    (hCong : ∀ x y, eqK x y = true → (p x).isKeep = (p y).isKeep)
    (left right : List K) :
    joinFilterMirrored eqK p left right = joinFilterLeftOnly eqK p left right := by
  dsimp only [joinFilterMirrored, joinFilterLeftOnly]
  cases evalFilterTable_total_of_infallible p hNoErrR right with | intro fr hFr =>
  rw [hFr]
  cases hFl : evalFilterTable p left
  · rfl
  · rename_i fl
    dsimp only []
    rw [evalInnerJoin_mirrored_aux eqK p hCong right fr hFr left fl hFl]

/-! ## 2. Full 4-Case `Option Nat` `LIMIT`/`OFFSET` Composition -/

noncomputable def dropRows {α : Type} : Nat → List α → List α
  | 0, xs => xs
  | Nat.succ _, [] => []
  | Nat.succ k, _ :: xs => dropRows k xs

noncomputable def takeRows {α : Type} : Nat → List α → List α
  | 0, _ => []
  | Nat.succ _, [] => []
  | Nat.succ k, x :: xs => x :: takeRows k xs

noncomputable def paginateOpt {α : Type} (optLim : Option Nat) (off : Nat) (xs : List α) : List α :=
  let dropped := dropRows off xs
  match optLim with
  | none     => dropped
  | some lim => takeRows lim dropped

def foldOptLimits (cLimOpt pLimOpt : Option Nat) (pOff : Nat) : Option Nat :=
  match cLimOpt, pLimOpt with
  | none, none           => none
  | none, some pLim      => some pLim
  | some cLim, none      => some (Nat.sub cLim pOff)
  | some cLim, some pLim =>
    let trunc := Nat.sub cLim pOff
    some (match Nat.ble pLim trunc with | true => pLim | false => trunc)

theorem dropRows_dropRows {α : Type} :
    ∀ (a b : Nat) (xs : List α), dropRows a (dropRows b xs) = dropRows (b + a) xs
  | 0, b, _ => by rw [Nat.add_zero b]; rfl
  | Nat.succ a, 0, _ => by rw [Nat.zero_add (Nat.succ a)]; rfl
  | Nat.succ _, Nat.succ _, [] => rfl
  | Nat.succ a, Nat.succ b, _ :: xs => by
    rw [Nat.succ_add b (Nat.succ a)]
    exact dropRows_dropRows (Nat.succ a) b xs

theorem dropRows_takeRows {α : Type} :
    ∀ (off lim : Nat) (xs : List α),
      dropRows off (takeRows lim xs) = takeRows (Nat.sub lim off) (dropRows off xs)
  | 0, lim, _ => by
    have h : Nat.sub lim 0 = lim := Nat.sub_zero lim
    rw [h]; rfl
  | Nat.succ o, 0, _ => by
    have h : Nat.sub 0 (Nat.succ o) = 0 := Nat.zero_sub (Nat.succ o)
    rw [h]; rfl
  | Nat.succ _, Nat.succ _, [] => by
    dsimp only [takeRows, dropRows]; cases Nat.sub _ _ <;> rfl
  | Nat.succ o, Nat.succ l, _ :: xs => by
    dsimp only [takeRows, dropRows]
    have h : Nat.sub (Nat.succ l) (Nat.succ o) = Nat.sub l o := Nat.succ_sub_succ l o
    rw [h]
    exact dropRows_takeRows o l xs

theorem takeRows_takeRows {α : Type} :
    ∀ (pLim cLim : Nat) (xs : List α),
      takeRows pLim (takeRows cLim xs) = takeRows (match Nat.ble pLim cLim with | true => pLim | false => cLim) xs
  | 0, _, _ => rfl
  | Nat.succ _, 0, _ => rfl
  | Nat.succ p, Nat.succ c, [] => by cases Nat.ble (Nat.succ p) (Nat.succ c) <;> rfl
  | Nat.succ p, Nat.succ c, _ :: xs => by
    dsimp only [takeRows]
    have hBle : Nat.ble (Nat.succ p) (Nat.succ c) = Nat.ble p c := rfl
    rw [hBle, takeRows_takeRows p c xs]
    cases Nat.ble p c <;> rfl

theorem foldProjectLimitAndOffset_all4_exact {α : Type}
    (cLimOpt pLimOpt : Option Nat) (cOff pOff : Nat) (xs : List α) :
    paginateOpt pLimOpt pOff (paginateOpt cLimOpt cOff xs) =
    paginateOpt (foldOptLimits cLimOpt pLimOpt pOff) (cOff + pOff) xs := by
  cases cLimOpt <;> cases pLimOpt
  · dsimp only [paginateOpt, foldOptLimits]
    exact dropRows_dropRows pOff cOff xs
  · rename_i pLim
    dsimp only [paginateOpt, foldOptLimits]
    rw [dropRows_dropRows pOff cOff xs]
  · rename_i cLim
    dsimp only [paginateOpt, foldOptLimits]
    rw [dropRows_takeRows pOff cLim (dropRows cOff xs)]
    rw [dropRows_dropRows pOff cOff xs]
  · rename_i cLim pLim
    dsimp only [paginateOpt, foldOptLimits]
    rw [dropRows_takeRows pOff cLim (dropRows cOff xs)]
    rw [dropRows_dropRows pOff cOff xs]
    exact takeRows_takeRows pLim (Nat.sub cLim pOff) (dropRows (cOff + pOff) xs)

/-! ## 3. Complete `googlesql::EvaluatorTableIterator` Typestate Machine (`evaluator_table_iterator.h:49-186`) -/

inductive IterPhase where
  | beforeFirstRow
  | onRow
  | exhaustedOk
  | exhaustedErr

inductive IterOp where
  | setColumnFilters  -- Valid only in `.beforeFirstRow` (`evaluator_table_iterator.h:133-136`)
  | setReadTime       -- Valid only in `.beforeFirstRow` (`evaluator_table_iterator.h:144-147`)
  | setDeadline       -- Valid only in `.beforeFirstRow` (`evaluator_table_iterator.h:176`)
  | nextRowHasMore    -- Valid in `.beforeFirstRow` or `.onRow` (`lines 152`)
  | nextRowEof        -- Valid in `.beforeFirstRow` or `.onRow`
  | nextRowError      -- Valid in `.beforeFirstRow` or `.onRow`
  | getValue          -- Valid only in `.onRow` (`lines 154-158`)
  | getStatus         -- Valid in all phases; returns OK unless `.exhaustedErr` (`lines 160-162`)
  | cancelAsync       -- Valid in all phases from any thread (`lines 170`)
  | inspectSchemaMem  -- `NumColumns`/`GetColumnName`/`GetColumnType`/`Get*MemoryUsage`: valid in all phases (`lines 54-65, 150-151, 180-186`)

def stepIterProtocol (phase : IterPhase) (op : IterOp) : Option IterPhase :=
  match op with
  | .getStatus        => some phase
  | .cancelAsync      => some phase
  | .inspectSchemaMem => some phase
  | .setColumnFilters => match phase with | .beforeFirstRow => some .beforeFirstRow | _ => none
  | .setReadTime      => match phase with | .beforeFirstRow => some .beforeFirstRow | _ => none
  | .setDeadline      => match phase with | .beforeFirstRow => some .beforeFirstRow | _ => none
  | .getValue         => match phase with | .onRow => some .onRow | _ => none
  | .nextRowHasMore   => match phase with | .beforeFirstRow | .onRow => some .onRow | _ => none
  | .nextRowEof       => match phase with | .beforeFirstRow | .onRow => some .exhaustedOk | _ => none
  | .nextRowError     => match phase with | .beforeFirstRow | .onRow => some .exhaustedErr | _ => none

def statusIsOk : IterPhase → Bool
  | .exhaustedErr => false
  | _             => true

theorem iterProtocol_full_conformance :
    stepIterProtocol .beforeFirstRow .getStatus = some .beforeFirstRow ∧
    stepIterProtocol .onRow .getStatus = some .onRow ∧
    statusIsOk .onRow = true ∧
    statusIsOk .exhaustedErr = false ∧
    stepIterProtocol .onRow .setReadTime = none ∧
    stepIterProtocol .onRow .setDeadline = none ∧
    stepIterProtocol .beforeFirstRow .getValue = none ∧
    stepIterProtocol .exhaustedOk .getValue = none ∧
    stepIterProtocol .exhaustedOk .nextRowHasMore = none ∧
    stepIterProtocol .exhaustedOk .cancelAsync = some .exhaustedOk :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SqlRewriteAndIteratorTypestate
