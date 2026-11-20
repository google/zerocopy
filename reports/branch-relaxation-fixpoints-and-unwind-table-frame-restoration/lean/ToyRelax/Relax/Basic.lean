import ToyRelax.Relax.Model

/-!
# Basic lemmas about the relaxation model

Proof infrastructure: monotonicity of addresses, the fixpoint characterization
of validity, and the potential function used for the termination bound.
-/

namespace Toy.Relax

variable {prm : Params} {p : Prog}

theorem Asg.Le.refl (a : Asg) : Asg.Le a a := fun _ h => h

theorem Asg.Le.trans {a b c : Asg} (h1 : Asg.Le a b) (h2 : Asg.Le b c) : Asg.Le a c :=
  fun i h => h2 i (h1 i h)

theorem Asg.Le.allShort (a : Asg) : Asg.Le allShort a := fun _ h => by cases h

theorem lt_length_of_getElem?_eq_some {i : Nat} {ins : Instr} (h : p[i]? = some ins) :
    i < p.length := by
  rcases Nat.lt_or_ge i p.length with hi | hi
  · exact hi
  · rw [List.getElem?_eq_none hi] at h; cases h

theorem outOfReach_eq_false_of_length_le {a : Asg} {i : Nat} (h : p.length ≤ i) :
    outOfReach prm p a i = false := by
  unfold outOfReach
  rw [List.getElem?_eq_none h]

theorem outOfReach_eq_true_iff {a : Asg} {i : Nat} :
    outOfReach prm p a i = true ↔
      ∃ t, p[i]? = some (.branch t) ∧ a i = false ∧ prm.reach < dist prm p a i t := by
  unfold outOfReach
  rcases hp : p[i]? with _ | ins
  · simp
  · cases ins with
    | fixed s => simp
    | align k => simp
    | branch t => simp

theorem outOfReach_eq_false_of_valid {a : Asg} (h : Valid prm p a) (i : Nat) :
    outOfReach prm p a i = false := by
  rcases Nat.lt_or_ge i p.length with hi | hi
  · exact h i hi
  · exact outOfReach_eq_false_of_length_le hi

/-- Short branches of a valid assignment are within reach. -/
theorem dist_le_reach_of_valid {a : Asg} (h : Valid prm p a) {i t : Nat}
    (hp : p[i]? = some (.branch t)) (ha : a i = false) : dist prm p a i t ≤ prm.reach := by
  have := outOfReach_eq_false_of_valid h i
  unfold outOfReach at this
  rw [hp] at this
  simp [ha] at this
  exact this

theorem le_step (a : Asg) : Asg.Le a (step prm p a) := by
  intro i h
  simp [step, h]

theorem step_eq_of_valid {a : Asg} (h : Valid prm p a) : step prm p a = a := by
  funext i
  simp [step, outOfReach_eq_false_of_valid h i]

theorem changed_eq_false_iff {a : Asg} : changed prm p a = false ↔ Valid prm p a := by
  unfold changed Valid
  simp [List.any_eq_false, List.mem_range]

theorem iter_succ' (f : Asg → Asg) (n : Nat) (a : Asg) : iter f (n + 1) a = f (iter f n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    show iter f (n + 1) (f a) = f (iter f (n + 1) a)
    rw [ih]
    rfl

theorem iter_add (f : Asg → Asg) (k m : Nat) (a : Asg) :
    iter f (k + m) a = iter f m (iter f k a) := by
  induction k generalizing a with
  | zero => simp [iter]
  | succ k ih =>
    rw [Nat.succ_add]
    exact ih (f a)

theorem iter_fix {f : Asg → Asg} {a : Asg} (h : f a = a) (n : Nat) : iter f n a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show iter f n (f a) = a
    rw [h, ih]

theorem le_iter_step (a : Asg) (n : Nat) : Asg.Le a (iter (step prm p) n a) := by
  induction n generalizing a with
  | zero => exact Asg.Le.refl a
  | succ n ih => exact Asg.Le.trans (le_step a) (ih (step prm p a))

/-! ### Potential: number of short branches -/

/-- Number of branch positions that are short under `a`. -/
def shortCount (p : Prog) (a : Asg) : Nat :=
  (List.range p.length).countP (fun i => isBranchAt p i && !a i)

theorem countP_range_isBranchAt (p : Prog) :
    (List.range p.length).countP (isBranchAt p) = p.countP Instr.isBranch := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map, List.countP_cons]
    have hfun : (isBranchAt (x :: p) ∘ Nat.succ) = isBranchAt p := by
      funext i
      simp [isBranchAt]
    rw [hfun, ih]
    simp [isBranchAt]

theorem shortCount_le_numBranches (a : Asg) : shortCount p a ≤ numBranches p := by
  unfold shortCount numBranches
  rw [← countP_range_isBranchAt]
  apply List.countP_mono_left
  intro x _ hx
  simp only [Bool.and_eq_true] at hx
  exact hx.1

theorem countP_lt_countP_of_le {l : List Nat} {P Q : Nat → Bool}
    (hle : ∀ x ∈ l, Q x = true → P x = true) {x : Nat} (hx : x ∈ l)
    (hP : P x = true) (hQ : Q x = false) : l.countP Q < l.countP P := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    have hle' : ∀ z ∈ l, Q z = true → P z = true := fun z hz => hle z (List.mem_cons_of_mem _ hz)
    have hmono : l.countP Q ≤ l.countP P := List.countP_mono_left hle'
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [hP, hQ]
      omega
    · have := ih hle' hx'
      by_cases hQy : Q y = true
      · have hPy := hle y (List.mem_cons_self) hQy
        simp [hQy, hPy]
        omega
      · simp only [Bool.not_eq_true] at hQy
        have h0 : (if Q y = true then 1 else 0) = 0 := by simp [hQy]
        rw [h0]
        have : 0 ≤ (if P y = true then 1 else 0) := Nat.zero_le _
        omega

theorem shortCount_step_lt {a : Asg} (h : changed prm p a = true) :
    shortCount p (step prm p a) < shortCount p a := by
  unfold changed at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hout⟩ := h
  obtain ⟨t, hpx, hax, _⟩ := outOfReach_eq_true_iff.mp hout
  unfold shortCount
  apply countP_lt_countP_of_le (x := x)
  · intro z _ hz
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hz ⊢
    refine ⟨hz.1, ?_⟩
    cases haz : a z
    · rfl
    · have := le_step (prm := prm) (p := p) a z haz
      rw [hz.2] at this
      cases this
  · exact hx
  · simp [isBranchAt, hpx, Instr.isBranch, hax]
  · simp [step, hout]

/-! ### Address monotonicity -/

theorem addr_mono_index (a : Asg) {i j : Nat} (h : i ≤ j) : addr prm p a i ≤ addr prm p a j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [addr_succ]; omega

theorem addr_sub_le_addr_sub {a b : Asg} {i t : Nat} (hit : i ≤ t)
    (h : ∀ j, i ≤ j → j < t → size prm p a j ≤ size prm p b j) :
    addr prm p a t - addr prm p a i ≤ addr prm p b t - addr prm p b i := by
  induction hit with
  | refl => simp
  | @step m hm ih =>
    have h1 := ih (fun j h1 h2 => h j h1 (by omega))
    have h2 := h m hm (by omega)
    have h3 := addr_mono_index (prm := prm) (p := p) a hm
    have h4 := addr_mono_index (prm := prm) (p := p) b hm
    rw [addr_succ, addr_succ]
    omega

theorem addr_le_addr_of_sizesMonotone (h : SizesMonotone prm p) {a b : Asg} (hab : Asg.Le a b)
    (k : Nat) : addr prm p a k ≤ addr prm p b k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [addr_succ, addr_succ]
    have := h a b hab k
    omega

theorem size_eq_zero_of_length_le (a : Asg) {k : Nat} (hk : p.length ≤ k) : size prm p a k = 0 := by
  unfold size
  rw [List.getElem?_eq_none hk]

theorem addr_eq_addr_length_of_length_le (a : Asg) {k : Nat} (hk : p.length ≤ k) :
    addr prm p a k = addr prm p a p.length := by
  induction hk with
  | refl => rfl
  | @step m hm ih =>
    rw [addr_succ, size_eq_zero_of_length_le a hm, ih]
    rfl

theorem addr_eq_addr_min (a : Asg) (k : Nat) :
    addr prm p a k = addr prm p a (min k p.length) := by
  rcases Nat.le_total k p.length with hk | hk
  · rw [Nat.min_eq_left hk]
  · rw [Nat.min_eq_right hk, addr_eq_addr_length_of_length_le a hk]

theorem addr_lt_addr_of_allSizesPositive (hpos : AllSizesPositive prm p) (a : Asg) {i j : Nat}
    (hij : i < j) (hj : j ≤ p.length) : addr prm p a i < addr prm p a j := by
  induction hij with
  | refl =>
    rw [addr_succ]
    have := hpos a i (by omega)
    omega
  | @step m hm ih =>
    rw [addr_succ]
    have := ih (by omega)
    omega

theorem addr_eq_iff_min_eq (hpos : AllSizesPositive prm p) (a : Asg) (x y : Nat) :
    addr prm p a x = addr prm p a y ↔ min x p.length = min y p.length := by
  constructor
  · intro h
    rw [addr_eq_addr_min a x, addr_eq_addr_min a y] at h
    rcases Nat.lt_trichotomy (min x p.length) (min y p.length) with hlt | heq | hgt
    · have := addr_lt_addr_of_allSizesPositive hpos a hlt (Nat.min_le_right _ _)
      omega
    · exact heq
    · have := addr_lt_addr_of_allSizesPositive hpos a hgt (Nat.min_le_right _ _)
      omega
  · intro h
    rw [addr_eq_addr_min a x, addr_eq_addr_min a y, h]

/-! ### Per-layout positivity -/

theorem addr_lt_addr_of_sizesPositiveAt {c : Asg} (hpos : SizesPositiveAt prm p c) {i j : Nat}
    (hij : i < j) (hj : j ≤ p.length) : addr prm p c i < addr prm p c j := by
  induction hij with
  | refl =>
    rw [addr_succ]
    have := hpos i (by omega)
    omega
  | @step m hm ih =>
    rw [addr_succ]
    have := ih (by omega)
    omega

theorem addr_eq_iff_min_eq_of_sizesPositiveAt {c : Asg} (hpos : SizesPositiveAt prm p c)
    (x y : Nat) : addr prm p c x = addr prm p c y ↔ min x p.length = min y p.length := by
  constructor
  · intro h
    rw [addr_eq_addr_min c x, addr_eq_addr_min c y] at h
    rcases Nat.lt_trichotomy (min x p.length) (min y p.length) with hlt | heq | hgt
    · have := addr_lt_addr_of_sizesPositiveAt hpos hlt (Nat.min_le_right _ _)
      omega
    · exact heq
    · have := addr_lt_addr_of_sizesPositiveAt hpos hgt (Nat.min_le_right _ _)
      omega
  · intro h
    rw [addr_eq_addr_min c x, addr_eq_addr_min c y, h]

/-! ### Address monotonicity from `shortSize ≤ longSize` alone

Alignment padding can shrink when code before it grows, but the *end* of an
alignment directive (`base + padTo k base`, the next multiple of `k`) is
monotone in `base`, so addresses are monotone in the assignment whenever a
long branch is at least as large as a short one. -/

theorem padTo_add_mono {k x y : Nat} (h : x ≤ y) : x + padTo k x ≤ y + padTo k y := by
  unfold padTo
  split
  · omega
  · next hk =>
    have hkp : 0 < k := Nat.pos_of_ne_zero hk
    have key : ∀ z : Nat, z + (k - z % k) % k = if z % k = 0 then z else (z / k + 1) * k := by
      intro z
      have hdiv := Nat.div_add_mod z k
      have hlt := Nat.mod_lt z hkp
      by_cases h0 : z % k = 0
      · simp [h0]
      · simp only [h0, ↓reduceIte]
        have hmod : (k - z % k) % k = k - z % k := Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        have : (z / k + 1) * k = k * (z / k) + k := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
        omega
    rw [key x, key y]
    have hqx := Nat.div_add_mod x k
    have hqy := Nat.div_add_mod y k
    have hmx := Nat.mod_lt x hkp
    have hmy := Nat.mod_lt y hkp
    have hdiv_le : x / k ≤ y / k := Nat.div_le_div_right h
    split <;> split
    · exact h
    · have : y ≤ (y / k + 1) * k := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
      omega
    · next hx0 hy0 =>
      have hlt : x / k < y / k := by
        rcases Nat.lt_or_eq_of_le hdiv_le with hlt | heq
        · exact hlt
        · rw [heq] at hqx
          omega
      have hmul : (x / k + 1) * k ≤ (y / k) * k := Nat.mul_le_mul_right k hlt
      rw [Nat.mul_comm (y / k) k] at hmul
      omega
    · exact Nat.mul_le_mul_right k (by omega)

theorem addr_le_addr_of_short_le_long (hsl : prm.shortSize ≤ prm.longSize) {a b : Asg}
    (hab : Asg.Le a b) (k : Nat) : addr prm p a k ≤ addr prm p b k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    simp only [addr]
    rcases p[k]? with _ | ins
    · exact ih
    · cases ins with
      | fixed s => simp only [instrSize]; omega
      | align m => simp only [instrSize]; exact padTo_add_mono ih
      | branch t =>
        simp only [instrSize]
        cases ha : a k
        · cases b k <;> simp <;> omega
        · rw [hab k ha]; simp; omega

/-! ### Values at non-branch positions do not matter -/

theorem addr_congr_of_eqOnBranches {c d : Asg} (h : ∀ i, isBranchAt p i = true → c i = d i) :
    ∀ k, addr prm p c k = addr prm p d k
  | 0 => rfl
  | k + 1 => by
    rw [addr_succ, addr_succ, addr_congr_of_eqOnBranches h k]
    congr 1
    unfold size
    rw [addr_congr_of_eqOnBranches h k]
    rcases hk : p[k]? with _ | ins
    · rfl
    · cases ins with
      | fixed s => rfl
      | align m => rfl
      | branch t =>
        have hck := h k (by simp [isBranchAt, hk, Instr.isBranch])
        simp only [instrSize, hck]

theorem valid_congr_of_eqOnBranches {c d : Asg} (h : ∀ i, isBranchAt p i = true → c i = d i) :
    Valid prm p c ↔ Valid prm p d := by
  have hout : ∀ i, outOfReach prm p c i = outOfReach prm p d i := by
    intro i
    unfold outOfReach
    rcases hi : p[i]? with _ | ins
    · rfl
    · cases ins with
      | fixed s => rfl
      | align m => rfl
      | branch t =>
        have hci := h i (by simp [isBranchAt, hi, Instr.isBranch])
        have hdist : dist prm p c i t = dist prm p d i t := by
          unfold dist
          rw [addr_congr_of_eqOnBranches h t, addr_congr_of_eqOnBranches h i]
        show (!c i && decide (prm.reach < dist prm p c i t)) =
          (!d i && decide (prm.reach < dist prm p d i t))
        rw [hci, hdist]
  unfold Valid
  simp only [hout]

end Toy.Relax
