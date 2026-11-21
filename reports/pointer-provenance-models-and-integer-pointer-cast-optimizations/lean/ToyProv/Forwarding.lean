import ToyProv.Lemmas
import ToyProv.Disjoint

/-!
# R4 — Store-to-load forwarding and dead-store elimination across an `int2ptr`

An optimizer that assumes "a pointer obtained from an integer does not alias this allocation"
is unsound in the exposed model (and in the flat model), and sound in the strict model, where
accesses through such pointers are UB. In the exposed model the right non-aliasing criterion is
provenance-based: the transformations are sound when the cast pointer's provenance differs from
the accessed pointer's in every reachable state, which holds in particular when the accessed
allocation was not exposed at the cast (R4e).
-/

namespace Toy.Prov

/-! ### R4a — forwarding across a store through a freshly cast pointer -/

/-- A at 16; `k := (int)A` (this exposes A); `v := 5`, `w := 9`. -/
def r4Pre : Prog := [.alloc 0 2, .ptr2int 2 0, .const 3 5, .const 4 9]
def r4Src : Prog := r4Pre ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]
def r4Tgt : Prog := r4Pre ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]

/-- **R4a.** Forwarding `v` to the load across `store r w`, where `r := int2ptr ((int)A)`, is not a
refinement in the exposed model: the cast picks A, so the source outputs `[9]` and the target
`[5]`. The same happens in the flat model. -/
theorem forwardAcrossCast_counterexample :
    ForwardAcrossCast .exposed r4Src r4Tgt ∧ ¬ Refines .exposed r4Tgt r4Src ∧
      beh .exposed r4Src = [.done [9]] ∧ beh .exposed r4Tgt = [.done [5]] ∧
      ForwardAcrossCast .flat r4Src r4Tgt ∧ ¬ Refines .flat r4Tgt r4Src ∧
      beh .flat r4Src = [.done [9]] ∧ beh .flat r4Tgt = [.done [5]] :=
  ⟨⟨r4Pre, [.obs 6], 5, 2, 0, 3, 4, 6, by decide, by decide, rfl, rfl, by decide⟩, by decide,
   by decide, by decide,
   ⟨r4Pre, [.obs 6], 5, 2, 0, 3, 4, 6, by decide, by decide, rfl, rfl, by decide⟩, by decide,
   by decide, by decide⟩

theorem forwardAcrossCast_not_sound_exposed : ¬ Sound .exposed ForwardAcrossCast :=
  fun h => forwardAcrossCast_counterexample.2.1 (h _ _ forwardAcrossCast_counterexample.1)

theorem forwardAcrossCast_not_sound_flat : ¬ Sound .flat ForwardAcrossCast :=
  fun h => forwardAcrossCast_counterexample.2.2.2.2.2.1 (h _ _ forwardAcrossCast_counterexample.2.2.2.2.1)

/-- As `r4Pre`, but `(int)A` is discarded and the cast's operand is the constant 16 (A's address
under the toy's deterministic allocator). -/
def r4PreGuess : Prog := [.alloc 0 2, .ptr2int 1 0, .const 2 16, .const 3 5, .const 4 9]

/-- **R4a, guessed address.** With A exposed by an unused cast, an `int2ptr` of the constant 16
also picks A, and forwarding fails the same way. This variant relies on the deterministic
allocator placing A at 16. -/
theorem forwardAcrossCast_counterexample_guessed_address :
    ForwardAcrossCast .exposed (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6])
      (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]) ∧
      ¬ Refines .exposed (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6])
        (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]) :=
  ⟨⟨r4PreGuess, [.obs 6], 5, 2, 0, 3, 4, 6, by decide, by decide, rfl, rfl, by decide⟩, by decide⟩

/-- **R4a, strict model.** The same pair is a refinement in the strict model only because the
source is UB there (the store through the provenance-less cast pointer); see
`forwardAcrossCast_strict_src_ub`. -/
theorem forwardAcrossCast_example_refines_strict :
    ForwardAcrossCast .strict r4Src r4Tgt ∧ Refines .strict r4Tgt r4Src ∧
      beh .strict r4Src = [.ub] ∧ beh .strict r4Tgt = [.ub] :=
  ⟨⟨r4Pre, [.obs 6], 5, 2, 0, 3, 4, 6, by decide, by decide, rfl, rfl, by decide⟩, by decide,
   by decide, by decide⟩

/-! ### R4b — dead-store elimination across a load through a freshly cast pointer -/

/-- A at 16 initialised to 1; `k := (int)A` (exposes A); `v := 5`, `w := 6`. -/
def r4dPre : Prog := [.alloc 0 2, .const 1 1, .store 0 1, .ptr2int 2 0, .const 3 5, .const 4 6]
def r4dSrc : Prog := r4dPre ++ [.int2ptr 5 2, .store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6]
def r4dTgt : Prog := r4dPre ++ [.int2ptr 5 2, .load 6 .int 5, .store 0 4] ++ [.obs 6]

/-- **R4b.** Deleting `store a v` because `a` is overwritten and the intervening load is through
a cast pointer is not a refinement in the exposed model: the load reads A, so the source
outputs `[5]` and the target `[1]`. The same happens in the flat model. -/
theorem dseAcrossCast_counterexample :
    DSEAcrossCast .exposed r4dSrc r4dTgt ∧ ¬ Refines .exposed r4dTgt r4dSrc ∧
      beh .exposed r4dSrc = [.done [5]] ∧ beh .exposed r4dTgt = [.done [1]] ∧
      DSEAcrossCast .flat r4dSrc r4dTgt ∧ ¬ Refines .flat r4dTgt r4dSrc ∧
      beh .flat r4dSrc = [.done [5]] ∧ beh .flat r4dTgt = [.done [1]] :=
  ⟨⟨r4dPre, [.obs 6], 5, 2, 0, 3, 6, .int, 4, by decide, by decide, by decide, rfl, rfl⟩, by decide,
   by decide, by decide,
   ⟨r4dPre, [.obs 6], 5, 2, 0, 3, 6, .int, 4, by decide, by decide, by decide, rfl, rfl⟩, by decide,
   by decide, by decide⟩

theorem dseAcrossCast_not_sound_exposed : ¬ Sound .exposed DSEAcrossCast :=
  fun h => dseAcrossCast_counterexample.2.1 (h _ _ dseAcrossCast_counterexample.1)

theorem dseAcrossCast_not_sound_flat : ¬ Sound .flat DSEAcrossCast :=
  fun h => dseAcrossCast_counterexample.2.2.2.2.2.1 (h _ _ dseAcrossCast_counterexample.2.2.2.2.1)

/-- **R4b, strict model.** The same pair is a refinement in the strict model only because the
source is UB there (the load through the provenance-less cast pointer); see
`dseAcrossCast_strict_src_ub`. -/
theorem dseAcrossCast_example_refines_strict :
    DSEAcrossCast .strict r4dSrc r4dTgt ∧ Refines .strict r4dTgt r4dSrc ∧
      beh .strict r4dSrc = [.ub] ∧ beh .strict r4dTgt = [.ub] :=
  ⟨⟨r4dPre, [.obs 6], 5, 2, 0, 3, 6, .int, 4, by decide, by decide, by decide, rfl, rfl⟩, by decide,
   by decide, by decide⟩

/-! ### The strict model: every program matching a cast window is UB -/

private theorem exec_strict_store_none_prov (s : St) (r w : Reg) (addr : Addr) (post : Prog)
    (hr : s.regs r = some (.ptr ⟨none, addr⟩)) :
    exec .strict (.store r w :: post) s = [none] := by
  simp only [exec, step, hr]
  cases s.regs w <;> simp [canAccess]

private theorem exec_strict_load_none_prov (s : St) (x r : Reg) (ty : Ty) (addr : Addr) (post : Prog)
    (hr : s.regs r = some (.ptr ⟨none, addr⟩)) :
    exec .strict (.load x ty r :: post) s = [none] := by
  simp only [exec, step, hr, canAccess]
  rfl

private theorem exec_strict_store_preserves_reg (s : St) (a v r : Reg) (val : Val) (post : Prog)
    (hr : s.regs r = some val)
    (hnext : ∀ s', s'.regs r = some val → exec .strict post s' = [none]) :
    exec .strict (.store a v :: post) s = [none] := by
  simp only [exec, step]
  cases s.regs a with
  | none => rfl
  | some va =>
    cases va with
    | int _ => rfl
    | ptr pa =>
      cases s.regs v with
      | none => rfl
      | some vv =>
        by_cases hacc : canAccess .strict s pa 2 = true
        · simp only [hacc, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          exact hnext { s with mem := writeBytes s.mem pa.addr (encodeVal vv) } hr
        · simp [hacc]

private theorem exec_strict_int2ptr_then (s : St) (r k : Reg) (post : Prog)
    (hnext : ∀ addr, exec .strict post (s.setReg r (.ptr ⟨none, addr⟩)) = [none]) :
    exec .strict (.int2ptr r k :: post) s = [none] := by
  simp only [exec, step]
  cases s.regs k with
  | none => rfl
  | some vk =>
    cases vk with
    | ptr _ => rfl
    | int addr =>
      simp only [castToPtr, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact hnext addr

private theorem exec_strict_none_after_prefix (pre W : Prog)
    (hW : ∀ s, exec .strict W s = [none]) : ∀ o ∈ exec .strict (pre ++ W) init, o = none := by
  rw [exec_append]
  intro o ho
  rw [List.mem_flatMap] at ho
  rcases ho with ⟨o1, _, ho1⟩
  cases o1 with
  | none => simpa using ho1
  | some s => simp only [hW s, List.mem_singleton] at ho1; exact ho1

/-- **Strict cast windows are UB (forwarding).** In the strict model, every source program matching
`ForwardAcrossCast` is UB: the store through `r := int2ptr k` uses a pointer without provenance.
(The target is UB too.) -/
theorem forwardAcrossCast_strict_src_ub (src tgt : Prog) (h : ForwardAcrossCast .strict src tgt) :
    beh .strict src = [.ub] ∧ beh .strict tgt = [.ub] := by
  rcases h with ⟨pre, post, r, k, a, v, w, x, -, -, rfl, rfl, -⟩
  have hW : ∀ (i : Instr) s, exec .strict (.int2ptr r k :: .store a v :: .store r w :: i :: post) s = [none] := by
    intro i s
    apply exec_strict_int2ptr_then
    intro addr
    apply exec_strict_store_preserves_reg _ a v r (.ptr ⟨none, addr⟩) _ (by simp [St.setReg])
    intro s' hr'
    exact exec_strict_store_none_prov s' r w addr _ hr'
  constructor
  · apply beh_ub_of_all_none
    have := exec_strict_none_after_prefix pre _ (hW (.load x .int a))
    simpa using this
  · apply beh_ub_of_all_none
    have := exec_strict_none_after_prefix pre _ (hW (.copy x v))
    simpa using this

/-- **Strict cast windows are UB (dead-store elimination).** In the strict model, every source
program matching `DSEAcrossCast` is UB: the load through `r := int2ptr k` uses a pointer without
provenance. (The target is UB too.) -/
theorem dseAcrossCast_strict_src_ub (src tgt : Prog) (h : DSEAcrossCast .strict src tgt) :
    beh .strict src = [.ub] ∧ beh .strict tgt = [.ub] := by
  rcases h with ⟨pre, post, r, k, a, v, x, ty, w, -, -, -, rfl, rfl⟩
  constructor
  · apply beh_ub_of_all_none
    have := exec_strict_none_after_prefix pre (.int2ptr r k :: .store a v :: .load x ty r :: .store a w :: post)
      (fun s => by
        apply exec_strict_int2ptr_then
        intro addr
        apply exec_strict_store_preserves_reg _ a v r (.ptr ⟨none, addr⟩) _ (by simp [St.setReg])
        intro s' hr'
        exact exec_strict_load_none_prov s' x r ty addr _ hr')
    simpa using this
  · apply beh_ub_of_all_none
    have := exec_strict_none_after_prefix pre (.int2ptr r k :: .load x ty r :: .store a w :: post)
      (fun s => by
        apply exec_strict_int2ptr_then
        intro addr
        exact exec_strict_load_none_prov _ x r ty addr _ (by simp [St.setReg]))
    simpa using this

/-! ### R4c — forwarding under a provenance-based non-aliasing hypothesis -/

private theorem expose_nil_eq (s : St) : s.expose [] = s := by
  cases s; simp [St.expose]

private theorem writeBytes_two_disjoint (mem : Addr → AByte) (ar aa : Addr) (bs : List AByte)
    (hbs : bs.length = 2) (hdisj : ar + 2 ≤ aa ∨ aa + 2 ≤ ar) :
    writeBytes mem ar bs aa = mem aa ∧ writeBytes mem ar bs (aa + 1) = mem (aa + 1) := by
  rcases bs with _ | ⟨b₀, bs⟩ <;> simp at hbs
  rcases bs with _ | ⟨b₁, bs⟩ <;> simp at hbs
  rcases bs with _ | ⟨b₂, bs⟩ <;> try (simp at hbs; done)
  dsimp only [Addr] at *
  simp only [writeBytes]
  constructor
  · split
    · rename_i h1; dsimp only [Addr] at h1; rcases hdisj with h | h <;> omega
    · split
      · rename_i h0; dsimp only [Addr] at h0; rcases hdisj with h | h <;> omega
      · rfl
  · split
    · rename_i h1; dsimp only [Addr] at h1; rcases hdisj with h | h <;> omega
    · split
      · rename_i h0; dsimp only [Addr] at h0; rcases hdisj with h | h <;> omega
      · rfl

private theorem writeBytes_two_get (mem : Addr → AByte) (aa : Addr) (b₀ b₁ : AByte) :
    writeBytes mem aa [b₀, b₁] aa = b₀ ∧ writeBytes mem aa [b₀, b₁] (aa + 1) = b₁ := by
  simp [writeBytes]


/-- **R4c.** In the exposed model, forwarding the stored integer `v` to the load of `a` across a
store through `r` is a refinement if, in every reachable state before the window, (`hne`) `r`
and `a` hold pointers of different provenance, and (`hv`) `v` holds an integer. No assumption is
made about how `r` was obtained (it may come from an `int2ptr`). -/
theorem forwardLoad_refines_exposed_of_provNe_of_isInt
    (pre post : Prog) (a v r w x : Reg)
    (hne : AllAfter .exposed pre (provNeC r a))
    (hv : AllAfter .exposed pre (isIntC v)) :
    Refines .exposed (pre ++ [.store a v, .store r w, .copy x v] ++ post)
      (pre ++ [.store a v, .store r w, .load x .int a] ++ post) := by
  apply refines_of_after_eq
  rw [after_eq_execOk, after_eq_execOk, execOk_append, execOk_append, execOk_append, execOk_append]
  congr 1
  apply flatMap_congr_mem
  intro s hs
  have hdisj := after_disjointBlocks .exposed pre s hs
  have hprov := hne s hs
  have hvis := hv s hs
  simp only [provNeC, ne_eq] at hprov
  simp only [isIntC] at hvis
  cases hrv : s.regs r with
  | none => simp [hrv] at hprov
  | some vr =>
    cases vr with
    | int _ => simp [hrv] at hprov
    | ptr xr =>
      cases hav : s.regs a with
      | none => simp [hrv, hav] at hprov
      | some va =>
        cases va with
        | int _ => simp [hrv, hav] at hprov
        | ptr xa =>
          simp only [hrv, hav] at hprov
          cases hvv : s.regs v with
          | none => simp [hvv] at hvis
          | some vv =>
            cases vv with
            | ptr _ => simp [hvv] at hvis
            | int nv =>
              rw [execOk_cons, execOk_cons]
              by_cases hacca : canAccess .exposed s xa 2 = true
              · have hst₁ : (step .exposed s (.store a v)).filterMap id =
                    [{ s with mem := writeBytes s.mem xa.addr [.intFrag nv 0, .intFrag nv 1] }] := by
                  simp [step, hav, hvv, hacca, encodeVal]
                rw [hst₁]
                simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
                let s₁ : St := { s with mem := writeBytes s.mem xa.addr [.intFrag nv 0, .intFrag nv 1] }
                rw [execOk_cons, execOk_cons]
                cases hwv : s.regs w with
                | none =>
                  have hsw : (step .exposed s₁ (.store r w)).filterMap id = [] := by
                    simp [step, s₁, hrv, hwv]
                  dsimp only [s₁] at hsw
                  simp only [hsw, List.flatMap_nil]
                | some vw =>
                  by_cases haccr : canAccess .exposed s xr 2 = true
                  · have haccr₁ : canAccess .exposed s₁ xr 2 = true := by
                      simpa [s₁, canAccess] using haccr
                    have hst₂ : (step .exposed s₁ (.store r w)).filterMap id =
                        [{ s₁ with mem := writeBytes s₁.mem xr.addr (encodeVal vw) }] := by
                      simp [step, s₁, hrv, hwv, haccr₁]
                    rw [hst₂]
                    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
                    let s₂ : St := { s₁ with mem := writeBytes s₁.mem xr.addr (encodeVal vw) }
                    have hacca₂ : canAccess .exposed s₂ xa 2 = true := by
                      simpa [s₂, s₁, canAccess] using hacca
                    have hdisj_bytes : xr.addr + 2 ≤ xa.addr ∨ xa.addr + 2 ≤ xr.addr := by
                      simp only [canAccess, lookup_eq_getElem?] at hacca haccr
                      cases hxa : xa.prov with
                      | none => simp [hxa] at hacca
                      | some ida =>
                        cases hxr : xr.prov with
                        | none => simp [hxr] at haccr
                        | some idr =>
                          simp only [hxa] at hacca; simp only [hxr] at haccr
                          cases hba : s.blocks[ida]? with
                          | none => simp [hba] at hacca
                          | some ba =>
                            cases hbr : s.blocks[idr]? with
                            | none => simp [hbr] at haccr
                            | some br =>
                              simp only [hba, inBlock, Bool.and_eq_true, decide_eq_true_eq] at hacca
                              simp only [hbr, inBlock, Bool.and_eq_true, decide_eq_true_eq] at haccr
                              rcases haccr with ⟨⟨_, haccr1⟩, haccr2⟩
                              rcases hacca with ⟨⟨_, hacca1⟩, hacca2⟩
                              rw [decide_eq_true_eq] at hprov
                              have hid : idr ≠ ida := fun e => hprov (by simp [hxr, hxa, e])
                              exact disjoint_two_bytes_of_ne hdisj hid hbr hba ⟨haccr1, haccr2⟩ ⟨hacca1, hacca2⟩
                    have hlen_vv_ok : (encodeVal vw).length = 2 := by cases vw <;> rfl
                    have ⟨hm₀, hm₁⟩ := writeBytes_two_disjoint s₁.mem xr.addr xa.addr
                      (encodeVal vw) hlen_vv_ok hdisj_bytes
                    have ⟨hs₁₀, hs₁₁⟩ := writeBytes_two_get s.mem xa.addr (.intFrag nv 0) (.intFrag nv 1)
                    have hmem₀ : s₂.mem xa.addr = .intFrag nv 0 := by simpa [s₂, s₁] using hm₀.trans hs₁₀
                    have hmem₁ : s₂.mem (xa.addr + 1) = .intFrag nv 1 := by simpa [s₂, s₁] using hm₁.trans hs₁₁
                    change execOk .exposed [.copy x v] s₂ = execOk .exposed [.load x .int a] s₂
                    rw [execOk_cons, execOk_cons]
                    have hcopy : (step .exposed s₂ (.copy x v)).filterMap id = [s₂.setReg x (.int nv)] := by
                      simp [step, s₂, s₁, hvv]
                    have hload : (step .exposed s₂ (.load x .int a)).filterMap id =
                        [s₂.setReg x (.int nv)] := by
                      have ha₂ : s₂.regs a = some (.ptr xa) := hav
                      simp only [step, ha₂, hacca₂, ↓reduceIte]
                      rw [hmem₀, hmem₁]
                      simp [decodeInt, expose_nil_eq]
                    simp only [hcopy, hload, List.flatMap_cons, List.flatMap_nil, List.append_nil, execOk_nil]
                  · have haccr₁ : canAccess .exposed s₁ xr 2 = false := by
                      have : canAccess .exposed s₁ xr 2 = canAccess .exposed s xr 2 := by
                        simp [s₁, canAccess]
                      rw [this]; cases h : canAccess .exposed s xr 2 <;> simp_all
                    have hsw : (step .exposed s₁ (.store r w)).filterMap id = [] := by
                      simp [step, s₁, hrv, hwv, haccr₁]
                    dsimp only [s₁] at hsw
                    simp only [hsw, List.flatMap_nil]
              · have hst₁ : (step .exposed s (.store a v)).filterMap id = [] := by
                  simp [step, hav, hvv, hacca]
                simp only [hst₁, List.flatMap_nil]

/-- **R4c, `hne` needed.** R4a's programs, with the window starting after the cast: `r` may carry
A's provenance. -/
theorem forwardLoad_provNe_needed :
    AllAfter .exposed (r4Pre ++ [.int2ptr 5 2]) (isIntC 3) ∧
      ¬ Refines .exposed (r4Pre ++ [.int2ptr 5 2] ++ [.store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6])
        (r4Pre ++ [.int2ptr 5 2] ++ [.store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]) :=
  ⟨by decide, by decide⟩

/-- A, B, `w := 9`; `v` is the pointer B. -/
def r4cPreV : Prog := [.alloc 0 2, .alloc 1 2, .const 4 9]

/-- **R4c, `hv` needed.** `v` is a pointer: the integer-typed load returns its address, while the
forwarded value is the pointer itself, on which the following integer comparison is UB. -/
theorem forwardLoad_isInt_needed :
    AllAfter .exposed r4cPreV (provNeC 1 0) ∧
      ¬ Refines .exposed (r4cPreV ++ [.store 0 1, .store 1 4, .copy 6 1] ++ [.intEq 7 6 6, .obs 7])
        (r4cPreV ++ [.store 0 1, .store 1 4, .load 6 .int 0] ++ [.intEq 7 6 6, .obs 7]) :=
  ⟨by decide, by decide⟩

/-- A (never exposed), B (exposed), `r := int2ptr (int)B`, `v := 5`, `w := 9`. -/
def r4cPreNV : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 2 1, .int2ptr 5 2, .const 3 5, .const 4 9]

/-- State after `alloc A; alloc B; k := (int)B` in the exposed model. -/
def r4cState : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 1] init with
  | some s :: _ => s
  | _ => init

/-- **R4c non-vacuity.** `r` comes from an `int2ptr`, both hypotheses hold, and the programs
output `[5]`. -/
theorem forwardLoad_nonvacuous :
    AllAfter .exposed r4cPreNV (provNeC 5 0) ∧ AllAfter .exposed r4cPreNV (isIntC 3) ∧
      beh .exposed (r4cPreNV ++ [.store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]) = [.done [5]] ∧
      beh .exposed (r4cPreNV ++ [.store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]) = [.done [5]] :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### R4d — dead-store elimination under a provenance-based non-aliasing hypothesis -/

private def stepRegDom (dom : Reg → Bool) : Instr → (Reg → Bool)
  | .alloc d _ | .load d _ _ | .ptr2int d _ | .int2ptr d _ | .ptrEq d _ _
  | .intEq d _ _ | .offset d _ _ | .const d _ | .copy d _ => fun r => if r = d then true else dom r
  | .free _ | .store _ _ | .memcpy _ _ _ | .obs _ => dom

private theorem step_regDom {m : Model} {s s' : St} {i : Instr}
    (h : some s' ∈ step m s i) :
    (fun r => (s'.regs r).isSome) = stepRegDom (fun r => (s.regs r).isSome) i := by
  have hcast : ∀ d a, some s' ∈ castToPtr m s d a →
      (fun r => (s'.regs r).isSome) = fun r => if r = d then true else (s.regs r).isSome := by
    intro d a hc
    cases m with
    | flat => simp [castToPtr] at hc; subst hc; funext r; simp [St.setReg]; split <;> simp_all
    | strict => simp [castToPtr] at hc; subst hc; funext r; simp [St.setReg]; split <;> simp_all
    | exposed =>
      simp only [castToPtr] at hc
      cases hcand : candidates s a with
      | nil => rw [hcand] at hc; simp at hc; subst hc; funext r; simp [St.setReg]; split <;> simp_all
      | cons c cs =>
        rw [hcand] at hc
        simp only [List.mem_map, Option.some.injEq] at hc
        obtain ⟨bid, -, heq⟩ := hc
        subst heq; funext r; simp [St.setReg]; split <;> simp_all
  cases i with
  | alloc d n =>
    by_cases hn : n = 0
    · simp [step, hn] at h
    · simp only [step, hn, ↓reduceIte, List.mem_singleton, Option.some.injEq] at h
      subst h; funext r; simp [stepRegDom, St.setReg]; split <;> simp_all
  | free p =>
    simp only [step] at h
    split at h <;> try (simp at h; done)
    split at h <;> simp at h; subst h; rfl
  | load d ty p =>
    simp only [step] at h
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    cases ty with
    | int =>
      simp only at h; split at h <;> simp at h; subst h
      funext r; simp [stepRegDom, St.setReg, St.expose]; split <;> simp_all
    | ptr =>
      simp only at h
      split at h
      · simp at h; subst h; funext r; simp [stepRegDom, St.setReg]; split <;> simp_all
      · exact hcast d _ h
      · simp at h
  | store p r =>
    simp only [step] at h
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    simp at h; subst h; rfl
  | memcpy d r n =>
    simp only [step] at h
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    simp at h; subst h; rfl
  | ptr2int d p =>
    simp only [step] at h
    split at h <;> simp at h; subst h
    funext r; simp [stepRegDom, St.setReg, St.expose]; split <;> simp_all
  | int2ptr d i =>
    simp only [step] at h
    split at h <;> try (simp at h; done)
    exact hcast d _ h
  | ptrEq d p q =>
    simp only [step] at h
    split at h <;> simp at h; subst h
    funext r; simp [stepRegDom, St.setReg]; split <;> simp_all
  | intEq d i j =>
    simp only [step] at h
    split at h <;> simp at h; subst h
    funext r; simp [stepRegDom, St.setReg]; split <;> simp_all
  | offset d p k =>
    simp only [step] at h
    split at h <;> try (simp at h; done)
    split at h <;> simp at h; subst h
    funext r; simp [stepRegDom, St.setReg]; split <;> simp_all
  | const d n =>
    simp only [step, List.mem_singleton, Option.some.injEq] at h
    subst h; funext r; simp [stepRegDom, St.setReg]; split <;> simp_all
  | copy d r =>
    simp only [step] at h
    split at h <;> simp at h; subst h
    funext r'; simp [stepRegDom, St.setReg]; split <;> simp_all
  | obs r =>
    simp only [step] at h
    cases hr : s.regs r with
    | none => simp [hr] at h
    | some v => cases v <;> (simp [hr] at h; subst h; rfl)

private theorem execOk_regDom {m : Model} {P : Prog} {s s' : St}
    (h : s' ∈ execOk m P s) :
    (fun r => (s'.regs r).isSome) = P.foldl stepRegDom (fun r => (s.regs r).isSome) := by
  induction P generalizing s with
  | nil => simp [execOk_nil] at h; subst h; rfl
  | cons i P ih =>
    rw [execOk_cons, List.mem_flatMap] at h
    rcases h with ⟨s₁, hs₁, hs'⟩
    rw [List.mem_filterMap] at hs₁
    rcases hs₁ with ⟨o, ho, ho_eq⟩
    cases o with
    | none => simp at ho_eq
    | some s₁' =>
      simp only [id_eq, Option.some.injEq] at ho_eq
      subst ho_eq
      rw [ih hs', step_regDom ho]
      rfl

private theorem writeBytes_overwrite_two (mem : Addr → AByte) (a : Addr) (b₀ b₁ c₀ c₁ : AByte) :
    writeBytes (writeBytes mem a [b₀, b₁]) a [c₀, c₁] = writeBytes mem a [c₀, c₁] := by
  funext z
  simp only [writeBytes]
  by_cases h1 : z = a + 1 <;> by_cases h0 : z = a <;> simp [h1, h0]


/-- **R4d.** In the exposed model, deleting `store a v` before `x := load ty r; store a w` is a
refinement if (`hne`) in every reachable state before the window `r` and `a` hold pointers of
different provenance, and (`hx`) the load does not overwrite the register `a`. -/
theorem dse_refines_exposed_of_provNe_of_ne
    (pre post : Prog) (a v r x w : Reg) (ty : Ty)
    (hne : AllAfter .exposed pre (provNeC r a))
    (hx : x ≠ a) :
    Refines .exposed (pre ++ [.load x ty r, .store a w] ++ post)
      (pre ++ [.store a v, .load x ty r, .store a w] ++ post) := by
  by_cases hv : ∃ s ∈ after .exposed pre, (s.regs v).isSome = true
  · rcases hv with ⟨s₀, hs₀, hv₀⟩
    apply refines_of_after_eq
    rw [after_eq_execOk, after_eq_execOk, execOk_append, execOk_append, execOk_append, execOk_append]
    congr 1
    apply flatMap_congr_mem
    intro s hs
    have hdisj := after_disjointBlocks .exposed pre s hs
    have hprov := hne s hs
    simp only [provNeC, ne_eq] at hprov
    have hdom : (s.regs v).isSome = true := by
      have h1 := congrFun (execOk_regDom hs) v
      have h0 := congrFun (execOk_regDom hs₀) v
      simpa [h1, h0] using hv₀
    cases hvv : s.regs v with
    | none => simp [hvv] at hdom
    | some vv =>
      cases hrv : s.regs r with
      | none => simp [hrv] at hprov
      | some vr =>
        cases vr with
        | int _ => simp [hrv] at hprov
        | ptr xr =>
          cases hav : s.regs a with
          | none => simp [hrv, hav] at hprov
          | some va =>
            cases va with
            | int _ => simp [hrv, hav] at hprov
            | ptr xa =>
              simp only [hrv, hav] at hprov
              rw [execOk_cons, execOk_cons]
              by_cases hacca : canAccess .exposed s xa 2 = true
              · have hst₁ : (step .exposed s (.store a v)).filterMap id =
                    [{ s with mem := writeBytes s.mem xa.addr (encodeVal vv) }] := by
                  simp [step, hav, hvv, hacca]
                rw [hst₁, List.flatMap_cons, List.flatMap_nil, List.append_nil]
                let s₁ : St := { s with mem := writeBytes s.mem xa.addr (encodeVal vv) }
                rw [execOk_cons]
                by_cases haccr : canAccess .exposed s xr 2 = true
                · have haccr₁ : canAccess .exposed s₁ xr 2 = true := by
                    simpa [s₁, canAccess] using haccr
                  have hdisj_bytes : xr.addr + 2 ≤ xa.addr ∨ xa.addr + 2 ≤ xr.addr := by
                    simp only [canAccess, lookup_eq_getElem?] at hacca haccr
                    cases hxa : xa.prov with
                    | none => simp [hxa] at hacca
                    | some ida =>
                      cases hxr : xr.prov with
                      | none => simp [hxr] at haccr
                      | some idr =>
                        simp only [hxa] at hacca; simp only [hxr] at haccr
                        cases hba : s.blocks[ida]? with
                        | none => simp [hba] at hacca
                        | some ba =>
                          cases hbr : s.blocks[idr]? with
                          | none => simp [hbr] at haccr
                          | some br =>
                            simp only [hba, inBlock, Bool.and_eq_true, decide_eq_true_eq] at hacca
                            simp only [hbr, inBlock, Bool.and_eq_true, decide_eq_true_eq] at haccr
                            rcases haccr with ⟨⟨_, haccr1⟩, haccr2⟩
                            rcases hacca with ⟨⟨_, hacca1⟩, hacca2⟩
                            rw [decide_eq_true_eq] at hprov
                            have hid : idr ≠ ida := fun e => hprov (by simp [hxr, hxa, e])
                            exact disjoint_two_bytes_of_ne hdisj hid hbr hba ⟨haccr1, haccr2⟩ ⟨hacca1, hacca2⟩
                  have hlen_vv : (encodeVal vv).length = 2 := by cases vv <;> rfl
                  have ⟨hm₀, hm₁⟩ := writeBytes_two_disjoint s.mem xa.addr xr.addr
                    (encodeVal vv) hlen_vv (Or.symm hdisj_bytes)
                  have hm₀' : s₁.mem xr.addr = s.mem xr.addr := hm₀
                  have hm₁' : s₁.mem (xr.addr + 1) = s.mem (xr.addr + 1) := hm₁
                  have hload_step : (step .exposed s₁ (.load x ty r)).filterMap id =
                      ((step .exposed s (.load x ty r)).filterMap id).map
                        (fun st => { st with mem := writeBytes st.mem xa.addr (encodeVal vv) }) := by
                    have hrv₁ : s₁.regs r = some (.ptr xr) := hrv
                    cases ty with
                    | int =>
                      simp only [step, hrv, hrv₁, haccr, haccr₁, hm₀', hm₁', ↓reduceIte]
                      cases decodeInt (s.mem xr.addr) (s.mem (xr.addr + 1)) with
                      | none => rfl
                      | some np => simp [s₁, St.setReg, St.expose]
                    | ptr =>
                      simp only [step, hrv, hrv₁, haccr, haccr₁, hm₀', hm₁', ↓reduceIte]
                      cases decodePtr (s.mem xr.addr) (s.mem (xr.addr + 1)) with
                      | none => rfl
                      | some res =>
                        cases res with
                        | inl q => simp [s₁, St.setReg]
                        | inr n =>
                          have hcand : candidates s₁ n = candidates s n := rfl
                          simp only [castToPtr, hcand]
                          cases candidates s n with
                          | nil => simp [s₁, St.setReg]
                          | cons c cs =>
                            have hfm : ∀ (f : AllocId → St) (l : List AllocId),
                                (l.map (fun id => some (f id))).filterMap id = l.map f := by
                              intro f l; induction l with | nil => rfl | cons a l ih => simp [ih]
                            rw [hfm (fun id => s₁.setReg x (.ptr ⟨some id, n⟩)) (c :: cs),
                              hfm (fun id => s.setReg x (.ptr ⟨some id, n⟩)) (c :: cs), List.map_map]
                            simp [Function.comp_def, s₁, St.setReg]
                  rw [hload_step, List.flatMap_map]
                  apply flatMap_congr_mem
                  intro st hst
                  have hst_mem : some st ∈ step .exposed s (.load x ty r) := by
                    rw [List.mem_filterMap] at hst
                    rcases hst with ⟨o, ho, ho_eq⟩
                    cases o with
                    | none => simp at ho_eq
                    | some st' =>
                      simp only [id_eq, Option.some.injEq] at ho_eq
                      subst ho_eq; exact ho
                  have hst_shape : ∃ val, st = s.setReg x val ∨ ∃ ps, st = (s.setReg x val).expose ps := by
                    cases ty with
                    | int =>
                      simp only [step, hrv, haccr, ↓reduceIte] at hst_mem
                      cases hdec : decodeInt (s.mem xr.addr) (s.mem (xr.addr + 1)) with
                      | none => simp [hdec] at hst_mem
                      | some np =>
                        simp [hdec] at hst_mem; subst hst_mem
                        exact ⟨.int np.1, Or.inr ⟨np.2, rfl⟩⟩
                    | ptr =>
                      simp only [step, hrv, haccr, ↓reduceIte] at hst_mem
                      cases hdec : decodePtr (s.mem xr.addr) (s.mem (xr.addr + 1)) with
                      | none => simp [hdec] at hst_mem
                      | some res =>
                        simp only [hdec] at hst_mem
                        cases res with
                        | inl q =>
                          simp at hst_mem; subst hst_mem
                          exact ⟨.ptr q, Or.inl rfl⟩
                        | inr n =>
                          simp only [castToPtr] at hst_mem
                          cases hcand : candidates s n with
                          | nil => simp [hcand] at hst_mem; subst hst_mem; exact ⟨.ptr ⟨none, n⟩, Or.inl rfl⟩
                          | cons c cs =>
                            rw [hcand] at hst_mem
                            simp only [List.mem_map, Option.some.injEq] at hst_mem
                            obtain ⟨bid, -, heq⟩ := hst_mem
                            subst heq; exact ⟨.ptr ⟨some bid, n⟩, Or.inl rfl⟩
                  rcases hst_shape with ⟨val, rfl | ⟨ps, rfl⟩⟩
                  · have hacca_st : canAccess .exposed (s.setReg x val) xa 2 = true := hacca
                    have hregs_a : (s.setReg x val).regs a = some (.ptr xa) := by
                      simp [St.setReg, Ne.symm hx, hav]
                    cases hwv : (s.setReg x val).regs w with
                    | none =>
                      simp [execOk_cons, step, hregs_a, hwv, List.flatMap_nil]
                    | some vw =>
                      have hacca_m : canAccess .exposed { (s.setReg x val) with
                          mem := writeBytes (s.setReg x val).mem xa.addr (encodeVal vv) } xa 2 = true := hacca
                      have hwb : writeBytes (writeBytes (s.setReg x val).mem xa.addr (encodeVal vv))
                          xa.addr (encodeVal vw) = writeBytes (s.setReg x val).mem xa.addr (encodeVal vw) := by
                        cases vv <;> cases vw <;> apply writeBytes_overwrite_two
                      simp [execOk_cons, execOk_nil, step, hregs_a, hacca_st, hacca_m, hwv, hwb,
                        List.flatMap_cons, List.flatMap_nil, List.append_nil]
                  · have hacca_st : canAccess .exposed ((s.setReg x val).expose ps) xa 2 = true := hacca
                    have hregs_a : ((s.setReg x val).expose ps).regs a = some (.ptr xa) := by
                      simp [St.expose, St.setReg, Ne.symm hx, hav]
                    cases hwv : ((s.setReg x val).expose ps).regs w with
                    | none =>
                      simp [execOk_cons, step, hregs_a, hwv, List.flatMap_nil]
                    | some vw =>
                      have hacca_m : canAccess .exposed { ((s.setReg x val).expose ps) with
                          mem := writeBytes ((s.setReg x val).expose ps).mem xa.addr (encodeVal vv) } xa 2 = true := hacca
                      have hwb : writeBytes (writeBytes ((s.setReg x val).expose ps).mem xa.addr (encodeVal vv))
                          xa.addr (encodeVal vw) =
                          writeBytes ((s.setReg x val).expose ps).mem xa.addr (encodeVal vw) := by
                        cases vv <;> cases vw <;> apply writeBytes_overwrite_two
                      simp [execOk_cons, execOk_nil, step, hregs_a, hacca_st, hacca_m, hwv, hwb,
                        List.flatMap_cons, List.flatMap_nil, List.append_nil]
                · have haccr₁ : canAccess .exposed s₁ xr 2 = false := by
                    have : canAccess .exposed s₁ xr 2 = canAccess .exposed s xr 2 := by
                      simp [s₁, canAccess]
                    rw [this]; cases h : canAccess .exposed s xr 2 <;> simp_all
                  have hld₁ : (step .exposed s₁ (.load x ty r)).filterMap id = [] := by
                    simp [step, s₁, hrv, haccr₁]
                  have hld : (step .exposed s (.load x ty r)).filterMap id = [] := by
                    simp [step, hrv, haccr]
                  dsimp only [s₁] at hld₁
                  simp only [hld₁, hld, List.flatMap_nil]
              · have hst₁ : (step .exposed s (.store a v)).filterMap id = [] := by
                  simp [step, hav, hvv, hacca]
                rw [hst₁, List.flatMap_nil]
                rw [List.flatMap_eq_nil_iff]
                intro st hst
                rw [List.mem_filterMap] at hst
                rcases hst with ⟨o, ho, ho_eq⟩
                cases o with
                | none => simp at ho_eq
                | some st' =>
                  simp only [id_eq, Option.some.injEq] at ho_eq
                  have hst_prop : st'.blocks = s.blocks ∧ st'.regs a = some (.ptr xa) := by
                    cases ty <;> simp only [step, hrv] at ho <;> split at ho <;> try (simp at ho; done)
                    · cases hdec : decodeInt (s.mem xr.addr) (s.mem (xr.addr + 1)) with
                      | none => simp [hdec] at ho
                      | some np => simp [hdec] at ho; subst ho; exact ⟨rfl, by simp [St.expose, St.setReg, Ne.symm hx, hav]⟩
                    · cases hdec : decodePtr (s.mem xr.addr) (s.mem (xr.addr + 1)) with
                      | none => simp [hdec] at ho
                      | some res =>
                        simp only [hdec] at ho
                        cases res with
                        | inl q => simp at ho; subst ho; exact ⟨rfl, by simp [St.setReg, Ne.symm hx, hav]⟩
                        | inr n =>
                          simp only [castToPtr] at ho
                          cases hcand : candidates s n with
                          | nil => simp [hcand] at ho; subst ho; exact ⟨rfl, by simp [St.setReg, Ne.symm hx, hav]⟩
                          | cons c cs =>
                            rw [hcand] at ho; simp only [List.mem_map, Option.some.injEq] at ho
                            obtain ⟨bid, -, heq⟩ := ho
                            subst heq; exact ⟨rfl, by simp [St.setReg, Ne.symm hx, hav]⟩
                  rw [← ho_eq, execOk_cons]
                  have hacca_st : canAccess .exposed st' xa 2 = false := by
                    simpa [canAccess, hst_prop.1] using hacca
                  cases hwv : st'.regs w <;> simp [step, hst_prop.2, hacca_st, hwv, List.flatMap_nil]
  · left
    rw [beh_eq_of_after]
    have hnone : ∀ s ∈ after .exposed pre, s.regs v = none := by
      intro s hs
      cases hrv : s.regs v with
      | none => rfl
      | some vv => exact absurd ⟨s, hs, by simp [hrv]⟩ hv
    have hem : after .exposed (pre ++ [.store a v, .load x ty r, .store a w] ++ post) = [] := by
      rw [after_eq_execOk, List.append_assoc, execOk_append, ← after_eq_execOk, List.flatMap_eq_nil_iff]
      intro s hs
      rw [execOk_append, execOk_cons]
      have hst : (step .exposed s (.store a v)).filterMap id = [] := by
        simp [step, hnone s hs]
      rw [hst, List.flatMap_nil, List.flatMap_nil]
    rw [hem]; simp

/-- **R4d, `hne` needed.** R4b's programs with the window starting after the cast. -/
theorem dse_provNe_needed :
    (6 : Reg) ≠ 0 ∧
      ¬ Refines .exposed (r4dPre ++ [.int2ptr 5 2] ++ [.load 6 .int 5, .store 0 4] ++ [.obs 6])
        (r4dPre ++ [.int2ptr 5 2] ++ [.store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6]) := by
  decide

/-- A (with an alias in register 8), B holding a pointer to C, `v := 5`, `w := 6`. -/
def r4dPreX : Prog := [.alloc 0 2, .copy 8 0, .alloc 1 2, .alloc 2 2, .store 1 2, .const 3 5, .const 4 6]

/-- **R4d, `hx` needed.** The load overwrites `a` with the pointer to C, so the second store goes
to C and the first store to A is not dead: the source outputs `[5]`, the target reads the
uninitialized A (UB). -/
theorem dse_ne_needed :
    AllAfter .exposed r4dPreX (provNeC 1 0) ∧
      ¬ Refines .exposed (r4dPreX ++ [.load 0 .ptr 1, .store 0 4] ++ [.load 6 .int 8, .obs 6])
        (r4dPreX ++ [.store 0 3, .load 0 .ptr 1, .store 0 4] ++ [.load 6 .int 8, .obs 6]) :=
  ⟨by decide, by decide⟩

/-- A (never exposed), B (exposed, initialised to 1), `r := int2ptr (int)B`, `v := 5`, `w := 6`. -/
def r4dPreNV : Prog :=
  [.alloc 0 2, .alloc 1 2, .const 9 1, .store 1 9, .ptr2int 2 1, .int2ptr 5 2, .const 3 5, .const 4 6]

/-- **R4d non-vacuity.** -/
theorem dse_nonvacuous :
    AllAfter .exposed r4dPreNV (provNeC 5 0) ∧ (6 : Reg) ≠ 0 ∧
      beh .exposed (r4dPreNV ++ [.store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6]) = [.done [1]] ∧
      beh .exposed (r4dPreNV ++ [.load 6 .int 5, .store 0 4] ++ [.obs 6]) = [.done [1]] :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### R4e — what an `int2ptr` can pick -/

/-- **R4e (exposed).** Every pointer an `int2ptr` of address `a` can produce in the exposed model
has address `a` and, if it has a provenance, that provenance is an exposed allocation (indeed a
candidate). Consequently, an allocation that is not exposed at the cast is never the provenance
of the result. -/
theorem int2ptr_exposed_result (s : St) (d k : Reg) (a : Nat) (hk : s.regs k = some (.int a)) :
    ∀ o ∈ step .exposed s (.int2ptr d k), ∃ x, o = some (s.setReg d (.ptr x)) ∧ x.addr = a ∧
      ∀ A, x.prov = some A → A ∈ candidates s a ∧ A ∈ s.exposed := by
  intro o ho
  simp only [step, hk, castToPtr] at ho
  split at ho
  · simp at ho
    exact ⟨⟨none, a⟩, ho, rfl, by simp⟩
  · rename_i c cs hcs
    simp only [List.mem_map] at ho
    obtain ⟨id, hid, rfl⟩ := ho
    refine ⟨⟨some id, a⟩, rfl, rfl, ?_⟩
    intro A hA
    simp only [Option.some.injEq] at hA
    subst hA
    rw [← hcs] at hid
    refine ⟨hid, ?_⟩
    simp only [candidates, List.mem_filter] at hid
    have := hid.2
    simp only [Bool.and_eq_true, List.contains_iff_mem] at this
    exact this.1

/-- **R4e, `hk` needed.** If the operand register does not hold an integer, the cast is UB
(its only successor is `none`). -/
theorem int2ptr_exposed_result_hk_needed :
    ¬ ∀ o ∈ step .exposed init (.int2ptr 0 1), ∃ x, o = some (init.setReg 0 (.ptr x)) ∧ x.addr = 0 := by
  simp [step, init]

/-- **R4e (strict).** In the strict model an `int2ptr` always produces a pointer without
provenance. -/
theorem int2ptr_strict_result (s : St) (d k : Reg) (a : Nat) (hk : s.regs k = some (.int a)) :
    step .strict s (.int2ptr d k) = [some (s.setReg d (.ptr ⟨none, a⟩))] := by
  simp [step, hk, castToPtr]

/-- **R4e (strict), `hk` needed.** -/
theorem int2ptr_strict_result_hk_needed :
    step .strict init (.int2ptr 0 1) ≠ [some (init.setReg 0 (.ptr ⟨none, 0⟩))] := by
  simp [step, init]

/-- **R4e non-vacuity.** After `k := (int)A` with A and B adjacent and both exposed, register 3
holds the integer 18 (A's one-past address = B's start), and the exposed-model cast has two
successors (A and B) while the strict-model cast has one. -/
def r4eState : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1] init with
  | some s :: _ => s
  | _ => init

theorem int2ptr_result_nonvacuous :
    r4eState.regs 3 = some (.int 18) ∧ (step .exposed r4eState (.int2ptr 5 3)).length = 2 ∧
      (step .strict r4eState (.int2ptr 5 3)).length = 1 := by
  decide

/-- **R4e, consequence for alias analysis.** In the exposed model, if register `a` holds a pointer
whose provenance `A` is not exposed at the cast, then after `d := int2ptr k` (with `d ≠ a`) the
two registers hold pointers of different provenance in every successor: the side condition
`provNeC d a` of R4c/R4d holds. -/
theorem int2ptr_result_provNe_of_not_exposed (s : St) (d k a : Reg) (n : Nat) (y : Ptr) (A : AllocId)
    (hk : s.regs k = some (.int n)) (ha : s.regs a = some (.ptr y)) (hA : y.prov = some A)
    (hnot : A ∉ s.exposed) (hda : d ≠ a) :
    ∀ o ∈ step .exposed s (.int2ptr d k), ∃ s', o = some s' ∧ provNeC d a s' = true := by
  intro o ho
  obtain ⟨x, rfl, -, hx⟩ := int2ptr_exposed_result s d k n hk o ho
  refine ⟨_, rfl, ?_⟩
  have hrd : (s.setReg d (.ptr x)).regs d = some (.ptr x) := by simp [St.setReg]
  have hra : (s.setReg d (.ptr x)).regs a = some (.ptr y) := by simp [St.setReg, Ne.symm hda, ha]
  simp only [provNeC, hrd, hra, decide_eq_true_eq]
  intro hxy
  rw [hA] at hxy
  exact hnot (hx A hxy).2

/-- **R4e consequence, non-vacuity.** A (never exposed) and B (exposed); casting B's address. -/
theorem int2ptr_result_provNe_nonvacuous :
    r4cState.regs 2 = some (.int 18) ∧ r4cState.regs 0 = some (.ptr ⟨some 0, 16⟩) ∧
      (⟨some 0, 16⟩ : Ptr).prov = some 0 ∧ (0 : AllocId) ∉ r4cState.exposed ∧ (5 : Reg) ≠ 0 ∧
      ∀ o ∈ step .exposed r4cState (.int2ptr 5 2), ∃ s', o = some s' ∧ provNeC 5 0 s' = true := by
  decide

/-! Tightness of the five hypotheses of `int2ptr_result_provNe_of_not_exposed`. Each theorem
fixes `s d k a n y A`, states that the other four hypotheses hold, and that the conclusion fails. -/

/-- **R4e consequence, `hk` needed.** Register 7 is unset, so the cast is UB: its only successor
is `none`. (`s = r4cState`, `d = 5`, `k = 7`, `a = 0`, `y = A's pointer`, `A = 0`.) -/
theorem int2ptr_result_provNe_hk_needed :
    r4cState.regs 7 = none ∧
      r4cState.regs 0 = some (.ptr ⟨some 0, 16⟩) ∧ (⟨some 0, 16⟩ : Ptr).prov = some 0 ∧
      (0 : AllocId) ∉ r4cState.exposed ∧ (5 : Reg) ≠ 0 ∧
      ¬ ∀ o ∈ step .exposed r4cState (.int2ptr 5 7), ∃ s', o = some s' ∧ provNeC 5 0 s' = true := by
  decide

/-- **R4e consequence, `ha` needed.** Register `a = 7` does not hold a pointer (it is unset), so
`provNeC 5 7` is false after the cast. (`s = r4cState`, `d = 5`, `k = 2`, `n = 18`,
`y = ⟨some 0, 16⟩`, `A = 0`.) -/
theorem int2ptr_result_provNe_ha_needed :
    r4cState.regs 2 = some (.int 18) ∧ r4cState.regs 7 = none ∧
      (⟨some 0, 16⟩ : Ptr).prov = some 0 ∧ (0 : AllocId) ∉ r4cState.exposed ∧ (5 : Reg) ≠ 7 ∧
      ¬ ∀ o ∈ step .exposed r4cState (.int2ptr 5 2), ∃ s', o = some s' ∧ provNeC 5 7 s' = true := by
  decide

/-- **R4e consequence, `hA` needed.** Register `a = 1` holds B's pointer, whose provenance is B
(exposed), not the unexposed A; the cast of B's address picks B, so `provNeC 5 1` is false.
(`s = r4cState`, `d = 5`, `k = 2`, `n = 18`, `y = ⟨some 1, 18⟩`, `A = 0`.) -/
theorem int2ptr_result_provNe_hA_needed :
    r4cState.regs 2 = some (.int 18) ∧ r4cState.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧
      (⟨some 1, 18⟩ : Ptr).prov ≠ some 0 ∧ (0 : AllocId) ∉ r4cState.exposed ∧ (5 : Reg) ≠ 1 ∧
      ¬ ∀ o ∈ step .exposed r4cState (.int2ptr 5 2), ∃ s', o = some s' ∧ provNeC 5 1 s' = true := by
  decide

/-- **R4e consequence, `hnot` needed.** In `r4eState` A is exposed; the cast of A's address 16
picks A, so `provNeC 5 0` is false. (`s = r4eState`, `d = 5`, `k = 2`, `n = 16`, `a = 0`,
`y = ⟨some 0, 16⟩`, `A = 0`.) -/
theorem int2ptr_result_provNe_hnot_needed :
    r4eState.regs 2 = some (.int 16) ∧ r4eState.regs 0 = some (.ptr ⟨some 0, 16⟩) ∧
      (⟨some 0, 16⟩ : Ptr).prov = some 0 ∧ (0 : AllocId) ∈ r4eState.exposed ∧ (5 : Reg) ≠ 0 ∧
      ¬ ∀ o ∈ step .exposed r4eState (.int2ptr 5 2), ∃ s', o = some s' ∧ provNeC 5 0 s' = true := by
  decide

/-- **R4e consequence, `hda` needed.** With `d = a = 0` the cast overwrites register 0, so
`provNeC 0 0` compares a register with itself and is false. (`s = r4cState`, `k = 2`, `n = 18`,
`y = ⟨some 0, 16⟩`, `A = 0`.) -/
theorem int2ptr_result_provNe_hda_needed :
    r4cState.regs 2 = some (.int 18) ∧ r4cState.regs 0 = some (.ptr ⟨some 0, 16⟩) ∧
      (⟨some 0, 16⟩ : Ptr).prov = some 0 ∧ (0 : AllocId) ∉ r4cState.exposed ∧
      ¬ ∀ o ∈ step .exposed r4cState (.int2ptr 0 2), ∃ s', o = some s' ∧ provNeC 0 0 s' = true := by
  decide

end Toy.Prov
