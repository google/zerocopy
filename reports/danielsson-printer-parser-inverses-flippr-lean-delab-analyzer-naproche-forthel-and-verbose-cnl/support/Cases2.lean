import Lean
set_option autoImplicit false

-- Case 2: parse the printed text back at the root namespace
#check ∀ {w : Nat} {h : 0 < 2 ^ w}, 0#'h = 0#w
open BitVec in
#check ∀ {w : Nat} {h : 0 < 2 ^ w}, 0#'h = 0#w

-- Case 1: re-elaborate the default-printed statement and show the binder type chosen for `h`
set_option pp.funBinderTypes true in
#check ∀ {α : Type} {β : Type} {xs : Array α} {f : (i : Nat) → α → i < xs.size → β}
  {ys : Array β}, xs.mapFinIdx f = ys ↔ ∃ h, ∀ (i : Nat) (h_1 : i < xs.size), ys[i] = f i xs[i] h_1
