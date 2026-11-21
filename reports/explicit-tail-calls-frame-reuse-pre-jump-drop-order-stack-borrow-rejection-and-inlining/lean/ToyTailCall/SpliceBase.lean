import ToyTailCall.Machine
import ToyTailCall.Inline
import ToyTailCall.Lemmas
import ToyTailCall.EscapeProof
import ToyTailCall.ReuseProof

/-!
# Proof support: frame embeddings for call-site splicing

A frame `F` of the original program *sits in* a frame `M` of the spliced program at slot offset
`off` (`Emb ρ off F M`) when every slot `s` of `F` corresponds to slot `s + off` of `M`: equal
drop flags, and values related by the frame-identity renaming `rv ρ` (which `Val.obs` erases).
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false

/-! ### Frame updates, pointwise -/

theorem get_kill (fr : Frame) (d s : Nat) : (fr.kill d).get s = fr.get s := rfl

theorem isLive_kill (fr : Frame) (d s : Nat) :
    (fr.kill d).isLive s = if s = d then false else fr.isLive s := by
  unfold Frame.kill Frame.isLive
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : s = d
  · subst h
    by_cases hl : s < fr.live.length
    · simp [hl]
    · simp [hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · simp [h, Ne.symm h]

theorem get_clear (fr : Frame) (d s : Nat) :
    (fr.clear d).get s = if s = d then .undef else fr.get s := by
  unfold Frame.clear Frame.get
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : s = d
  · subst h
    by_cases hl : s < fr.vals.length
    · simp [hl]
    · simp [hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · simp [h, Ne.symm h]

theorem isLive_clear (fr : Frame) (d s : Nat) :
    (fr.clear d).isLive s = if s = d then false else fr.isLive s := by
  unfold Frame.clear Frame.isLive
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : s = d
  · subst h
    by_cases hl : s < fr.live.length
    · simp [hl]
    · simp [hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · simp [h, Ne.symm h]

theorem get_write (fr : Frame) {d : Nat} (v : Val) (hd : d < fr.vals.length) (s : Nat) :
    (fr.write d v).get s = if s = d then v else fr.get s := by
  unfold Frame.write Frame.get
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : s = d
  · subst h; simp [hd]
  · simp [h, Ne.symm h]

theorem isLive_write (fr : Frame) {d : Nat} (v : Val) (hd : d < fr.live.length) (s : Nat) :
    (fr.write d v).isLive s = if s = d then true else fr.isLive s := by
  unfold Frame.write Frame.isLive
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : s = d
  · subst h; simp [hd]
  · simp [h, Ne.symm h]

theorem isLive_of_ge (fr : Frame) {s : Nat} (h : fr.live.length ≤ s) : fr.isLive s = false := by
  unfold Frame.isLive
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem get_of_ge (fr : Frame) {s : Nat} (h : fr.vals.length ≤ s) : fr.get s = .undef := by
  unfold Frame.get
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

@[simp] theorem kill_vals (fr : Frame) (d : Nat) : (fr.kill d).vals = fr.vals := rfl
@[simp] theorem kill_fid (fr : Frame) (d : Nat) : (fr.kill d).fid = fr.fid := rfl
@[simp] theorem kill_fn (fr : Frame) (d : Nat) : (fr.kill d).fn = fr.fn := rfl
@[simp] theorem kill_pc (fr : Frame) (d : Nat) : (fr.kill d).pc = fr.pc := rfl
@[simp] theorem kill_cont (fr : Frame) (d : Nat) : (fr.kill d).cont = fr.cont := rfl
@[simp] theorem kill_pendingRet (fr : Frame) (d : Nat) : (fr.kill d).pendingRet = fr.pendingRet := rfl
@[simp] theorem kill_live_length (fr : Frame) (d : Nat) :
    (fr.kill d).live.length = fr.live.length := by simp [Frame.kill]

@[simp] theorem write_vals_length (fr : Frame) (d : Nat) (v : Val) :
    (fr.write d v).vals.length = fr.vals.length := by simp [Frame.write]
@[simp] theorem write_live_length (fr : Frame) (d : Nat) (v : Val) :
    (fr.write d v).live.length = fr.live.length := by simp [Frame.write]
@[simp] theorem write_fid (fr : Frame) (d : Nat) (v : Val) : (fr.write d v).fid = fr.fid := rfl
@[simp] theorem write_fn (fr : Frame) (d : Nat) (v : Val) : (fr.write d v).fn = fr.fn := rfl
@[simp] theorem write_pc (fr : Frame) (d : Nat) (v : Val) : (fr.write d v).pc = fr.pc := rfl
@[simp] theorem write_cont (fr : Frame) (d : Nat) (v : Val) : (fr.write d v).cont = fr.cont := rfl
@[simp] theorem write_pendingRet (fr : Frame) (d : Nat) (v : Val) :
    (fr.write d v).pendingRet = fr.pendingRet := rfl

@[simp] theorem clear_vals_length (fr : Frame) (d : Nat) :
    (fr.clear d).vals.length = fr.vals.length := by simp [Frame.clear]
@[simp] theorem clear_live_length (fr : Frame) (d : Nat) :
    (fr.clear d).live.length = fr.live.length := by simp [Frame.clear]
@[simp] theorem clear_fid (fr : Frame) (d : Nat) : (fr.clear d).fid = fr.fid := rfl
@[simp] theorem clear_fn (fr : Frame) (d : Nat) : (fr.clear d).fn = fr.fn := rfl
@[simp] theorem clear_pc (fr : Frame) (d : Nat) : (fr.clear d).pc = fr.pc := rfl
@[simp] theorem clear_cont (fr : Frame) (d : Nat) : (fr.clear d).cont = fr.cont := rfl
@[simp] theorem clear_pendingRet (fr : Frame) (d : Nat) :
    (fr.clear d).pendingRet = fr.pendingRet := rfl

/-- `dropList` only changes drop flags. -/
theorem dropList_shape (fn : Fn) (fr : Frame) (ss : List Nat) (unw : Bool) :
    (dropList fn fr ss unw).1 = { fr with live := (dropList fn fr ss unw).1.live } ∧
      (dropList fn fr ss unw).1.live.length = fr.live.length := by
  induction ss generalizing fr unw with
  | nil => simp [dropList]
  | cons s ss ih =>
    simp only [dropList]
    split
    · split
      · simp [Frame.kill]
      · obtain ⟨h1, h2⟩ := ih (fr.kill s) true
        refine ⟨?_, by rw [h2]; simp⟩
        rw [h1]; rfl
    · obtain ⟨h1, h2⟩ := ih (fr.kill s) unw
      refine ⟨?_, by rw [h2]; simp⟩
      rw [h1]; rfl

/-! ### Values -/

/-- Rename the frame identity of a pointer: `ρ fid = (fid', off)` sends slot `j` of frame `fid`
to slot `j + off` of frame `fid'`. -/
def rv (ρ : Nat → Nat × Nat) : Val → Val
  | .int n => .int n
  | .ptr f j => .ptr (ρ f).1 (j + (ρ f).2)
  | .undef => .undef

@[simp] theorem rv_obs (ρ : Nat → Nat × Nat) (v : Val) : (rv ρ v).obs = v.obs := by
  cases v <;> rfl

@[simp] theorem rv_undef (ρ : Nat → Nat × Nat) : rv ρ .undef = .undef := rfl
@[simp] theorem rv_int (ρ : Nat → Nat × Nat) (n : Nat) : rv ρ (.int n) = .int n := rfl

/-- Every pointer in `v` names a frame below `N`. -/
def PtrLt (N : Nat) : Val → Prop
  | .ptr f _ => f < N
  | _ => True

theorem rv_congr {ρ ρ' : Nat → Nat × Nat} {N : Nat} (h : ∀ x, x < N → ρ' x = ρ x) {v : Val}
    (hv : PtrLt N v) : rv ρ' v = rv ρ v := by
  cases v with
  | ptr f j => simp only [rv, h f hv]
  | _ => rfl

theorem ptrLt_mono {N N' : Nat} (h : N ≤ N') {v : Val} (hv : PtrLt N v) : PtrLt N' v := by
  cases v with
  | ptr f j => exact Nat.lt_of_lt_of_le hv h
  | _ => trivial

theorem ptrLt_get {N : Nat} {fr : Frame} (h : ∀ v ∈ fr.vals, PtrLt N v) (s : Nat) :
    PtrLt N (fr.get s) := by
  rcases get_cases fr s with hm | he
  · exact h _ hm
  · rw [he]; trivial

/-! ### Embeddings -/

/-- Frame `F` sits in frame `M` at slot offset `off`. -/
structure Emb (ρ : Nat → Nat × Nat) (off : Nat) (F M : Frame) : Prop where
  len : F.vals.length + off ≤ M.vals.length
  get : ∀ s : Nat, s < F.vals.length → M.get (s + off) = rv ρ (F.get s)
  live : ∀ s : Nat, s < F.vals.length → M.isLive (s + off) = F.isLive s

theorem out_ne {s off t n : Nat} (hs : s < n) (ht : t < off ∨ n + off ≤ t) : s + off ≠ t := by
  rcases ht with ht | ht <;> omega

theorem Emb.congr {ρ : Nat → Nat × Nat} {off : Nat} {F M F' M' : Frame} (h : Emb ρ off F M)
    (hF : F'.vals = F.vals) (hFl : F'.live = F.live) (hM : M'.vals = M.vals)
    (hMl : M'.live = M.live) : Emb ρ off F' M' := by
  refine ⟨by rw [hF, hM]; exact h.len, fun s hs => ?_, fun s hs => ?_⟩
  · have := h.get s (by rw [← hF]; exact hs)
    unfold Frame.get at *; rw [hF, hM]; exact this
  · have := h.live s (by rw [← hF]; exact hs)
    unfold Frame.isLive at *; rw [hFl, hMl]; exact this

theorem Emb.congr_rho {ρ ρ' : Nat → Nat × Nat} {N off : Nat} {F M : Frame} (h : Emb ρ off F M)
    (hρ : ∀ x, x < N → ρ' x = ρ x) (hv : ∀ v ∈ F.vals, PtrLt N v) : Emb ρ' off F M :=
  ⟨h.len, fun s hs => by rw [h.get s hs, rv_congr hρ (ptrLt_get hv s)], h.live⟩

theorem Emb.kill {ρ : Nat → Nat × Nat} {off : Nat} {F M : Frame} (h : Emb ρ off F M) (s : Nat) :
    Emb ρ off (F.kill s) (M.kill (s + off)) := by
  refine ⟨by simpa using h.len, fun t ht => ?_, fun t ht => ?_⟩
  · simp only [get_kill]; exact h.get t (by simpa using ht)
  · simp only [isLive_kill]
    have := h.live t (by simpa using ht)
    by_cases hts : t = s
    · subst hts; simp
    · have : t + off ≠ s + off := by omega
      simp [hts, this, h.live t (by simpa using ht)]

theorem Emb.kill_out {ρ : Nat → Nat × Nat} {off : Nat} {F M : Frame} (h : Emb ρ off F M)
    {t : Nat} (ht : t < off ∨ F.vals.length + off ≤ t) : Emb ρ off F (M.kill t) := by
  refine ⟨by simpa using h.len, fun s hs => ?_, fun s hs => ?_⟩
  · simp only [get_kill]; exact h.get s hs
  · have : s + off ≠ t := out_ne hs ht
    simp only [isLive_kill, this, ↓reduceIte]; exact h.live s hs

theorem Emb.clear {ρ : Nat → Nat × Nat} {off : Nat} {F M : Frame} (h : Emb ρ off F M) (d : Nat) :
    Emb ρ off (F.clear d) (M.clear (d + off)) := by
  refine ⟨by simpa using h.len, fun t ht => ?_, fun t ht => ?_⟩
  · simp only [clear_vals_length] at ht
    simp only [get_clear]
    by_cases htd : t = d
    · subst htd; simp
    · have : t + off ≠ d + off := by omega
      simp [htd, this, h.get t ht]
  · simp only [clear_vals_length] at ht
    simp only [isLive_clear]
    by_cases htd : t = d
    · subst htd; simp
    · have : t + off ≠ d + off := by omega
      simp [htd, this, h.live t ht]

theorem Emb.clear_out {ρ : Nat → Nat × Nat} {off : Nat} {F M : Frame} (h : Emb ρ off F M)
    {t : Nat} (ht : t < off ∨ F.vals.length + off ≤ t) : Emb ρ off F (M.clear t) := by
  refine ⟨by simpa using h.len, fun s hs => ?_, fun s hs => ?_⟩
  · have : s + off ≠ t := out_ne hs ht
    simp only [get_clear, this, ↓reduceIte]; exact h.get s hs
  · have : s + off ≠ t := out_ne hs ht
    simp only [isLive_clear, this, ↓reduceIte]; exact h.live s hs

theorem Emb.write {ρ : Nat → Nat × Nat} {off : Nat} {F M : Frame} (h : Emb ρ off F M) {d : Nat}
    (v : Val) (hd : d < F.vals.length) (hFl : F.live.length = F.vals.length)
    (hMl : M.live.length = M.vals.length) :
    Emb ρ off (F.write d v) (M.write (d + off) (rv ρ v)) := by
  have hdM : d + off < M.vals.length := by have := h.len; omega
  refine ⟨by simpa using h.len, fun t ht => ?_, fun t ht => ?_⟩
  · simp only [write_vals_length] at ht
    rw [get_write _ _ hdM, get_write _ _ hd]
    by_cases htd : t = d
    · subst htd; simp
    · have : t + off ≠ d + off := by omega
      simp [htd, this, h.get t ht]
  · simp only [write_vals_length] at ht
    rw [isLive_write _ _ (by omega), isLive_write _ _ (by omega)]
    by_cases htd : t = d
    · subst htd; simp
    · have : t + off ≠ d + off := by omega
      simp [htd, this, h.live t ht]

theorem Emb.write_out {ρ : Nat → Nat × Nat} {off : Nat} {F M : Frame} (h : Emb ρ off F M)
    {t : Nat} (w : Val) (ht : t < off ∨ F.vals.length + off ≤ t) (htM : t < M.vals.length)
    (hMl : M.live.length = M.vals.length) : Emb ρ off F (M.write t w) := by
  refine ⟨by simpa using h.len, fun s hs => ?_, fun s hs => ?_⟩
  · have : s + off ≠ t := out_ne hs ht
    rw [get_write _ _ htM]; simp only [this, ↓reduceIte]; exact h.get s hs
  · have : s + off ≠ t := out_ne hs ht
    rw [isLive_write _ _ (by omega)]; simp only [this, ↓reduceIte]; exact h.live s hs

theorem Emb.foldl_clear {ρ : Nat → Nat × Nat} {off : Nat} :
    ∀ (ss : List Nat) (F M : Frame), Emb ρ off F M →
      Emb ρ off (ss.foldl Frame.clear F) ((ss.map (· + off)).foldl Frame.clear M)
  | [], _, _, h => h
  | d :: ss, F, M, h => by
    simp only [List.foldl_cons, List.map_cons]
    exact Emb.foldl_clear ss _ _ (h.clear d)

theorem Emb.foldl_clear_out {ρ : Nat → Nat × Nat} {off : Nat} {F : Frame} :
    ∀ (ts : List Nat) (M : Frame), Emb ρ off F M →
      (∀ t ∈ ts, t < off ∨ F.vals.length + off ≤ t) → Emb ρ off F (ts.foldl Frame.clear M)
  | [], _, h, _ => h
  | t :: ts, M, h, ht => by
    simp only [List.foldl_cons]
    exact Emb.foldl_clear_out ts _ (h.clear_out (ht t (List.mem_cons_self ..)))
      (fun t' h' => ht t' (List.mem_cons_of_mem _ h'))

theorem foldl_clear_fields :
    ∀ (ss : List Nat) (fr : Frame),
      (ss.foldl Frame.clear fr).fid = fr.fid ∧ (ss.foldl Frame.clear fr).fn = fr.fn ∧
      (ss.foldl Frame.clear fr).pc = fr.pc ∧ (ss.foldl Frame.clear fr).cont = fr.cont ∧
      (ss.foldl Frame.clear fr).pendingRet = fr.pendingRet ∧
      (ss.foldl Frame.clear fr).vals.length = fr.vals.length ∧
      (ss.foldl Frame.clear fr).live.length = fr.live.length
  | [], _ => by simp
  | d :: ss, fr => by
    simp only [List.foldl_cons]
    have := foldl_clear_fields ss (fr.clear d)
    simpa using this

theorem foldl_clear_get :
    ∀ (ss : List Nat) (fr : Frame) (s : Nat),
      (ss.foldl Frame.clear fr).get s = if s ∈ ss then .undef else fr.get s
  | [], _, _ => by simp
  | d :: ss, fr, s => by
    simp only [List.foldl_cons, foldl_clear_get ss (fr.clear d) s, get_clear, List.mem_cons]
    by_cases h1 : s ∈ ss
    · simp [h1]
    · by_cases h2 : s = d <;> simp [h1, h2]

theorem foldl_clear_isLive :
    ∀ (ss : List Nat) (fr : Frame) (s : Nat),
      (ss.foldl Frame.clear fr).isLive s = if s ∈ ss then false else fr.isLive s
  | [], _, _ => by simp
  | d :: ss, fr, s => by
    simp only [List.foldl_cons, foldl_clear_isLive ss (fr.clear d) s, isLive_clear, List.mem_cons]
    by_cases h1 : s ∈ ss
    · simp [h1]
    · by_cases h2 : s = d <;> simp [h1, h2]

/-! ### Finalization at an offset -/

/-- Dropping the slots `l` of `F` and the slots `l + off` of `M`, where `F` sits in `M` at
`off` and the destructors correspond, emits the same events and ends the same way. -/
theorem dropList_sim {ρ : Nat → Nat × Nat} {off : Nat} (fn fn' : Fn) :
    ∀ (l : List Nat) (F M : Frame) (unw : Bool), Emb ρ off F M →
      (∀ s ∈ l, s < F.vals.length) → (∀ s ∈ l, fn'.dtor (s + off) = fn.dtor s) →
      (dropList fn' M (l.map (· + off)) unw).2 = (dropList fn F l unw).2 ∧
      Emb ρ off (dropList fn F l unw).1 (dropList fn' M (l.map (· + off)) unw).1 ∧
      ∀ t, (t < off ∨ F.vals.length + off ≤ t) →
        (dropList fn' M (l.map (· + off)) unw).1.isLive t = M.isLive t
  | [], F, M, unw, h, _, _ => by simp [dropList]; exact h
  | s :: l, F, M, unw, h, hl, hd => by
    have hs : s < F.vals.length := hl s (List.mem_cons_self ..)
    have hd0 : fn'.dtor (s + off) = fn.dtor s := hd s (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x < (F.kill s).vals.length := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hd' : ∀ x ∈ l, fn'.dtor (x + off) = fn.dtor x := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    have hk := h.kill s
    have hev : (M.get (s + off)).obs = (F.get s).obs := by rw [h.get s hs, rv_obs]
    have hout : ∀ t, (t < off ∨ F.vals.length + off ≤ t) → (M.kill (s + off)).isLive t = M.isLive t := by
      intro t ht
      have : t ≠ s + off := fun e => out_ne hs ht e.symm
      simp [isLive_kill, this]
    simp only [List.map_cons, dropList, hd0, hev]
    by_cases hp : (fn.dtor s == .panics) = true
    · simp only [hp, ↓reduceIte]
      cases unw with
      | true => simp only [↓reduceIte]; exact ⟨by trivial, hk, hout⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨a, b, c⟩ := dropList_sim fn fn' l (F.kill s) (M.kill (s + off)) true hk hl' hd'
        refine ⟨by rw [a], b, fun t ht => ?_⟩
        rw [c t (by simpa using ht), hout t ht]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨a, b, c⟩ := dropList_sim fn fn' l (F.kill s) (M.kill (s + off)) unw hk hl' hd'
      refine ⟨by rw [a], b, fun t ht => ?_⟩
      rw [c t (by simpa using ht), hout t ht]

/-- `dropList` while unwinding over a concatenation. -/
theorem dropList_append_true (fn : Fn) :
    ∀ (fr : Frame) (l1 l2 : List Nat),
      dropList fn fr (l1 ++ l2) true =
        if (dropList fn fr l1 true).2.2 = .abort then dropList fn fr l1 true
        else ((dropList fn (dropList fn fr l1 true).1 l2 true).1,
          (dropList fn fr l1 true).2.1 ++ (dropList fn (dropList fn fr l1 true).1 l2 true).2.1,
          (dropList fn (dropList fn fr l1 true).1 l2 true).2.2)
  | fr, [], l2 => by simp [dropList]
  | fr, s :: l1, l2 => by
    simp only [List.cons_append, dropList]
    by_cases hp : (fn.dtor s == .panics) = true
    · simp [hp]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      rw [dropList_append_true fn (fr.kill s) l1 l2]
      split <;> simp_all

theorem dropList_true_ne_ok (fn : Fn) :
    ∀ (fr : Frame) (l : List Nat), (dropList fn fr l true).2.2 ≠ .ok
  | fr, [] => by simp [dropList]
  | fr, s :: l => by
    simp only [dropList]
    split
    · simp
    · exact dropList_true_ne_ok fn (fr.kill s) l

/-! ### Pending drops -/

theorem range_reverse_split (n e : Nat) :
    (List.range (n + e)).reverse =
      ((List.range e).map (n + ·)).reverse ++ (List.range n).reverse := by
  rw [List.range_add, List.reverse_append]

/-- The pending drops of a frame that extends `F` by slots holding no pending drop. -/
theorem pendingDrops_ext {ρ : Nat → Nat × Nat} {fn fn' : Fn} {F F' : Frame} (h : Emb ρ 0 F F')
    (hd : ∀ s, s < F.vals.length → fn'.dtor s = fn.dtor s)
    (hext : ∀ s, F.vals.length ≤ s → F'.isLive s = true → fn'.dtor s = .none) :
    pendingDrops fn' F' = pendingDrops fn F := by
  unfold pendingDrops
  have hlen := h.len
  obtain ⟨e, he⟩ : ∃ e, F'.vals.length = F.vals.length + e := ⟨F'.vals.length - F.vals.length, by omega⟩
  rw [he, range_reverse_split, List.filter_append]
  have h1 : (((List.range e).map (F.vals.length + ·)).reverse.filter
      fun s => F'.isLive s && fn'.dtor s != .none) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp only [List.mem_reverse, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    cases hl : F'.isLive (F.vals.length + i)
    · simp
    · simp [hext _ (by omega) hl]
  rw [h1, List.nil_append]
  apply List.filter_congr
  intro x hx
  simp only [List.mem_reverse, List.mem_range] at hx
  have := h.live x hx
  simp only [Nat.add_zero] at this
  rw [this, hd x hx]

end Toy.TailCall.SpliceProof
