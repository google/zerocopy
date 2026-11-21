import ToyPacked.Hyps

/-!
# Lemmas used in the proofs of the main results
-/

namespace Toy.Packed

/-! ## Sequencing -/

/-- Every event of an outcome satisfies `p`. -/
def AllEv (p : Ev → Prop) (o : Out) : Prop := ∀ e, e ∈ o.evs → p e

theorem allEv_nil (p : Ev → Prop) (ok : Bool) : AllEv p ⟨[], ok⟩ := by
  intro e he; cases he

theorem allEv_single {p : Ev → Prop} {e : Ev} (ok : Bool) (h : p e) : AllEv p ⟨[e], ok⟩ := by
  intro e' he'; simp at he'; subst he'; exact h

theorem allEv_andThen {p : Ev → Prop} {o : Out} {g : Unit → Out} (h1 : AllEv p o)
    (h2 : o.ok = true → AllEv p (g ())) : AllEv p (o.andThen g) := by
  unfold Out.andThen
  split
  · rename_i hok
    intro e he
    simp only [List.mem_append] at he
    exact he.elim (h1 e) (h2 hok e)
  · exact h1

/-- Folds of `andThen` preserve any relation that sequencing preserves. -/
theorem foldl_andThen_rel {α : Type} (R : Out → Out → Prop)
    (hR : ∀ (o1 o2 : Out) (g1 g2 : Unit → Out), R o1 o2 → (o1.ok = true → R (g1 ()) (g2 ())) →
      R (o1.andThen g1) (o2.andThen g2))
    (f1 f2 : α → Out) :
    ∀ (l : List α) (acc1 acc2 : Out), (∀ x, x ∈ l → R (f1 x) (f2 x)) → R acc1 acc2 →
      R (l.foldl (fun acc x => acc.andThen fun _ => f1 x) acc1)
        (l.foldl (fun acc x => acc.andThen fun _ => f2 x) acc2)
  | [], _, _, _, hacc => hacc
  | x :: tl, acc1, acc2, hstep, hacc => by
    simp only [List.foldl_cons]
    exact foldl_andThen_rel R hR f1 f2 tl _ _ (fun y hy => hstep y (List.mem_cons_of_mem x hy))
      (hR _ _ _ _ hacc (fun _ => hstep x (List.mem_cons_self ..)))

/-- Folds of `andThen` preserve `AllEv p`. -/
theorem foldl_andThen_allEv {α : Type} (p : Ev → Prop) (f : α → Out) (l : List α) (acc : Out)
    (hstep : ∀ x, x ∈ l → AllEv p (f x)) (hacc : AllEv p acc) :
    AllEv p (l.foldl (fun acc x => acc.andThen fun _ => f x) acc) :=
  foldl_andThen_rel (fun o _ => AllEv p o)
    (fun _ _ _ _ h1 h2 => allEv_andThen h1 h2) f f l acc acc hstep hacc

theorem mem_zipIdx_fst {α : Type} :
    ∀ (l : List α) (k : Nat) (x : α) (j : Nat), (x, j) ∈ l.zipIdx k → x ∈ l
  | [], _, _, _, h => by simp at h
  | a :: tl, k, x, j, h => by
    simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | htl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem a (mem_zipIdx_fst tl (k + 1) x j htl)

/-! ## Monotonicity in the fuel -/

theorem needsDrop_mono (env : Env) :
    ∀ f1 f2 t, f1 ≤ f2 → needsDrop env f1 t = true → needsDrop env f2 t = true
  | 0, _, _, _, h => by simp [needsDrop] at h
  | _ + 1, 0, _, hle, _ => by omega
  | f1 + 1, f2 + 1, t, hle, h => by
    simp only [needsDrop] at h ⊢
    cases hk : (env.ty t).kind <;> simp [hk] at h ⊢
    rcases h with ⟨f, hmem, hnd⟩
    exact ⟨f, hmem, needsDrop_mono env f1 f2 f (by omega) hnd⟩

theorem callsShim_mono (env : Env) (f1 f2 : Nat) (k : ShimKind) (u : Nat) (hle : f1 ≤ f2)
    (h : callsShim env f1 k u = true) : callsShim env f2 k u = true := by
  cases k with
  | dropGlue => exact needsDrop_mono env f1 f2 u hle h
  | boxFree => exact h
  | clone => exact h

theorem addrBlind_anti (env : Env) :
    ∀ f1 f2 t, f1 ≤ f2 → AddrBlind env f2 t = true → AddrBlind env f1 t = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, hle, _ => by omega
  | f1 + 1, f2 + 1, t, hle, h => by
    simp only [AddrBlind] at h ⊢
    cases hk : (env.ty t).kind <;> simp [hk] at h ⊢
    · exact h
    · intro f hf; exact addrBlind_anti env f1 f2 f (by omega) (h f hf)

/-! ## Environment facts -/

theorem lt_length_of_ne_default {env : Env} {t : Nat} (h : env.ty t ≠ default) :
    t < env.length := by
  cases Nat.lt_or_ge t env.length with
  | inl hlt => exact hlt
  | inr hge =>
    exact absurd (by simp [Env.ty, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]) h

theorem agg_lt_length {env : Env} {t : Nat} {pack : Option Nat} {fs : List Nat}
    (h : (env.ty t).kind = .agg pack fs) : t < env.length :=
  lt_length_of_ne_default (fun hd => by rw [hd] at h; cases h)

theorem lt_length_of_align_ne_one {env : Env} {t : Nat} (h : env.align t ≠ 1) :
    t < env.length :=
  lt_length_of_ne_default (fun hd => h (by simp [Env.align, hd]; rfl))

/-! ## Reachable shims and positions -/

theorem mem_reach_self (env : Env) (f : Nat) (k : ShimKind) (t : Nat) :
    (k, t) ∈ reach env (f + 1) k t := by
  simp [reach]

theorem reach_box_sub (env : Env) (f t p : Nat) (hk : (env.ty t).kind = .box p)
    (hnd : needsDrop env f p = true) :
    ∀ x, x ∈ reach env f .dropGlue p → x ∈ reach env (f + 1) .dropGlue t := by
  intro x hx
  simp only [reach, hk, hnd, ↓reduceIte, List.mem_cons]
  exact Or.inr hx

theorem reach_field_sub (env : Env) (f : Nat) (k : ShimKind) (t : Nat) (pack : Option Nat)
    (fs : List Nat) (fld : Nat) (hkb : k ≠ .boxFree) (hk : (env.ty t).kind = .agg pack fs)
    (hmem : fld ∈ fs) (hcs : callsShim env f k fld = true) :
    ∀ x, x ∈ reach env f k fld → x ∈ reach env (f + 1) k t := by
  intro x hx
  cases k with
  | dropGlue =>
    simp only [reach, hk, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨fld, hmem, by simp only [callsShim] at hcs; simp [hcs, hx]⟩
  | boxFree => exact absurd rfl hkb
  | clone =>
    simp only [reach, hk, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨fld, hmem, hx⟩

theorem mem_reachableShims_of_root (P : Prog) (op : Op) (hop : op ∈ P.src) (r : ShimKind × Nat)
    (hr : op.shimRoot P = some r) :
    ∀ x, x ∈ reach P.env P.fuel r.1 r.2 → x ∈ reachableShims P := by
  intro x hx
  simp only [reachableShims, List.mem_flatMap, List.mem_filterMap]
  exact ⟨r, ⟨op, hop, hr⟩, hx⟩

theorem mem_positions_body (P : Prog) (f : Nat) (k : ShimKind) (t : Nat) (pack : Option Nat)
    (fs : List Nat) (fld j : Nat) (hkb : k ≠ .boxFree) (hk : (P.env.ty t).kind = .agg pack fs)
    (hmem : (fld, j) ∈ fs.zipIdx) (hle : f ≤ P.fuel) (hcs : callsShim P.env f k fld = true)
    (hR : (k, t) ∈ reachableShims P) :
    ⟨.shim k t, j + 1, k, P.env.align t, t, [j], fld, P.layout t j⟩ ∈ positions P := by
  apply List.mem_append_right
  simp only [shimPositions, List.mem_flatMap]
  refine ⟨(k, t), hR, ?_⟩
  have hcs' := callsShim_mono P.env f P.fuel k fld hle hcs
  cases k with
  | boxFree => exact absurd rfl hkb
  | dropGlue =>
    simp only [bodyPositions, List.mem_filterMap]
    exact ⟨(fld, j), by simpa [Env.fields, hk] using hmem, by simp [hcs']⟩
  | clone =>
    simp only [bodyPositions, List.mem_filterMap]
    exact ⟨(fld, j), by simpa [Env.fields, hk] using hmem, by simp [hcs']⟩

theorem mem_srcPositions (P : Prog) (k : ShimKind) (p : Place) (i u o : Nat)
    (hmem : (Op.comp k p, i) ∈ P.src.zipIdx)
    (hroot : p.root < P.locals.length)
    (hres : resolve P.env P.layout (P.locals.getD p.root 0) p.path = some (u, o))
    (hcs : callsShim P.env P.fuel k u = true) :
    ⟨.src, i, k, P.env.align (P.locals.getD p.root 0), P.locals.getD p.root 0, p.path, u, o⟩ ∈
      positions P := by
  apply List.mem_append_left
  simp only [srcPositions, List.mem_filterMap]
  refine ⟨(.comp k p, i), hmem, ?_⟩
  simp only [hroot, ↓reduceIte, hres, hcs]

/-! ## A generic invariant for `compStep` and `runShim` -/

theorem compStep_allEv (p : Ev → Prop) (call : Nat → Nat → VName → Out) (env : Env) (fuel : Nat)
    (cfg : Cfg) (k : ShimKind) (b : BodyId) (i A t0 : Nat) (path : List Nat) (u a : Nat)
    (n : VName) (hcopy : p (.copy n))
    (h : callsShim env fuel k u = true →
      (cfg.crit k A t0 path = true →
        ((env.ty u).sized = true → AllEv p (call u (cfg.tmp b i) n)) ∧
        ((env.ty u).sized = false → p (.stuck b i))) ∧
      (cfg.crit k A t0 path = false → AllEv p (call u a n))) :
    AllEv p (compStep call env fuel cfg k b i A t0 path u a n) := by
  unfold compStep
  split
  · rename_i hcs
    have h' := h hcs
    split
    · rename_i hcr
      split
      · rename_i hsz
        exact allEv_andThen (allEv_single _ hcopy) (fun _ => (h'.1 hcr).1 hsz)
      · rename_i hsz
        exact allEv_single _ ((h'.1 hcr).2 (by simpa using hsz))
    · rename_i hcr
      exact h'.2 (by simpa using hcr)
  · exact allEv_nil _ _

/-- A generic invariant for `runShim`: if an invariant `Inv fuel k t a` on shim entries makes
op `0` satisfy `p` and is passed on to every nested shim entry, every event satisfies `p`. -/
theorem runShim_allEv (m : Mode) (cfg : Cfg) (env : Env) (L : Layout) (p : Ev → Prop)
    (Inv : Nat → ShimKind → Nat → Nat → Prop)
    (hfuel : p .outOfFuel)
    (hev : ∀ (n : VName) (a : Nat), p (.dtor n) ∧ p (.addrObs n a) ∧ p (.free n) ∧ p (.cloned n) ∧
      p (.copy n))
    (href : ∀ f k t a, Inv (f + 1) k t a → shimExists env k t = true →
      AllEv p (refStep m cfg (.shim k t) 0 (env.align t) a))
    (hbox : ∀ f t a q, Inv (f + 1) .dropGlue t a → (env.ty t).kind = .box q →
      needsDrop env f q = true → Inv f .dropGlue q (heapAddr env q))
    (hfield : ∀ f k t a pack fs fld j, k ≠ .boxFree → Inv (f + 1) k t a →
      (env.ty t).kind = .agg pack fs → (fld, j) ∈ fs.zipIdx → callsShim env f k fld = true →
      (cfg.crit k (env.align t) t [j] = true →
        ((env.ty fld).sized = true → Inv f k fld (cfg.tmp (.shim k t) (j + 1))) ∧
        ((env.ty fld).sized = false → p (.stuck (.shim k t) (j + 1)))) ∧
      (cfg.crit k (env.align t) t [j] = false → Inv f k fld (a + L t j))) :
    ∀ fuel k t a n, Inv fuel k t a → AllEv p (runShim m cfg env L fuel k t a n)
  | 0, _, _, _, _, _ => by simp only [runShim]; exact allEv_single _ hfuel
  | f + 1, k, t, a, n, hinv => by
    simp only [runShim]
    split
    · rename_i hex
      refine allEv_andThen (href f k t a hinv hex) (fun _ => ?_)
      have IH := runShim_allEv m cfg env L p Inv hfuel hev href hbox hfield f
      -- the agg case, shared by drop glue and clone shims
      have hagg : ∀ (k' : ShimKind) (pack : Option Nat) (fs : List Nat), k' = k → k' ≠ .boxFree →
          (env.ty t).kind = .agg pack fs →
          AllEv p (seqFields fs fun fld j =>
            compStep (fun u a' n' => runShim m cfg env L f k' u a' n') env f cfg k'
              (.shim k' t) (j + 1) (env.align t) t [j] fld (a + L t j) (n.child j)) := by
        intro k' pack fs hkk hkb hk
        subst hkk
        unfold seqFields
        refine foldl_andThen_allEv p _ fs.zipIdx _ (fun q hq => ?_) (allEv_nil _ _)
        rcases q with ⟨fld, j⟩
        refine compStep_allEv p _ env f cfg k' _ _ _ _ _ fld _ _ (hev _ 0).2.2.2.2 (fun hcs => ?_)
        have hf := hfield f k' t a pack fs fld j hkb hinv hk hq hcs
        exact ⟨fun hcr => ⟨fun hsz => IH _ _ _ _ ((hf.1 hcr).1 hsz), (hf.1 hcr).2⟩,
          fun hcr => IH _ _ _ _ (hf.2 hcr)⟩
      cases k with
      | dropGlue =>
        cases hk : (env.ty t).kind with
        | scalar => exact allEv_nil _ _
        | res o =>
          intro e he
          cases o
          · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at he
            subst he; exact (hev n a).1
          · simp only [↓reduceIte, List.singleton_append, List.mem_cons, List.not_mem_nil,
              or_false] at he
            rcases he with rfl | rfl
            · exact (hev n a).2.1
            · exact (hev n a).1
        | box q =>
          refine allEv_andThen ?_ (fun _ => allEv_single _ (hev n 0).2.2.1)
          split
          · rename_i hnd
            exact IH _ _ _ _ (hbox f t a q hinv hk hnd)
          · exact allEv_nil _ _
        | agg pack fs => exact hagg .dropGlue pack fs rfl (by decide) hk
      | boxFree => exact allEv_single _ (hev n 0).2.2.1
      | clone =>
        cases hk : (env.ty t).kind with
        | agg pack fs => exact hagg .clone pack fs rfl (by decide) hk
        | scalar => exact allEv_single _ (hev n 0).2.2.2.1
        | res _ => exact allEv_single _ (hev n 0).2.2.2.1
        | box _ => exact allEv_single _ (hev n 0).2.2.2.1
    · exact allEv_nil _ _

/-! ## Source places and shim roots -/

theorem place_some {P : Prog} {p : Place} {A t0 u a : Nat}
    (h : P.place p = some (A, t0, u, a)) :
    ∃ o, p.root < P.locals.length ∧
      resolve P.env P.layout (P.locals.getD p.root 0) p.path = some (u, o) ∧
      A = P.env.align (P.locals.getD p.root 0) ∧ t0 = P.locals.getD p.root 0 ∧
      a = P.frame.getD p.root 0 + o := by
  unfold Prog.place at h
  by_cases hroot : p.root < P.locals.length
  · cases hres : resolve P.env P.layout (P.locals.getD p.root 0) p.path with
    | none => simp only [hroot, ↓reduceIte, hres, reduceCtorEq] at h
    | some r =>
      obtain ⟨u', o'⟩ := r
      simp only [hroot, ↓reduceIte, hres, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨o', hroot, rfl, rfl, rfl, rfl⟩
  · simp [hroot] at h

theorem shimRoot_comp {P : Prog} {k : ShimKind} {p : Place} {A t0 u a : Nat}
    (h : P.place p = some (A, t0, u, a)) (hcs : callsShim P.env P.fuel k u = true) :
    (Op.comp k p).shimRoot P = some (k, u) := by
  simp [Op.shimRoot, h, hcs]

theorem shimRoot_rawCall (P : Prog) (k : ShimKind) (t a : Nat) (hex : shimExists P.env k t = true) :
    (Op.rawCall k t a).shimRoot P = some (k, t) := by
  simp [Op.shimRoot, hex]

/-- Running a shim that does not exist, with positive fuel, produces no event and continues. -/
theorem runShim_succ_missing (m : Mode) (cfg : Cfg) (env : Env) (L : Layout) (fuel : Nat)
    (k : ShimKind) (t a : Nat) (n : VName) (hex : shimExists env k t = false) :
    runShim m cfg env L (fuel + 1) k t a n = ⟨[], true⟩ := by
  simp [runShim, hex]

/-- A raw call that passes `ClientPtrsAligned` passes an aligned pointer to an existing shim. -/
theorem ptrAligned_rawCall {env : Env} {k : ShimKind} {t a : Nat}
    (h : (Op.rawCall k t a).ptrAligned env = true) (hex : shimExists env k t = true) :
    env.align t ∣ a := by
  simpa [Op.ptrAligned, hex] using h

/-- Shim entries a run of `P` may make: within the fuel bound, and every shim reachable from the
entry is among the program's reachable shims. -/
def Reached (P : Prog) (fuel : Nat) (k : ShimKind) (t : Nat) : Prop :=
  fuel ≤ P.fuel ∧ ∀ x, x ∈ reach P.env fuel k t → x ∈ reachableShims P

theorem reached_root (P : Prog) (op : Op) (hop : op ∈ P.src) (k : ShimKind) (t : Nat)
    (hr : op.shimRoot P = some (k, t)) : Reached P P.fuel k t :=
  ⟨Nat.le_refl _, mem_reachableShims_of_root P op hop (k, t) hr⟩

theorem reached_box {P : Prog} {f t q : Nat} (h : Reached P (f + 1) .dropGlue t)
    (hk : (P.env.ty t).kind = .box q) (hnd : needsDrop P.env f q = true) :
    Reached P f .dropGlue q :=
  ⟨by have := h.1; omega, fun x hx => h.2 x (reach_box_sub P.env f t q hk hnd x hx)⟩

theorem reached_field {P : Prog} {f : Nat} {k : ShimKind} {t : Nat} {pack : Option Nat}
    {fs : List Nat} {fld j : Nat} (h : Reached P (f + 1) k t) (hkb : k ≠ .boxFree)
    (hk : (P.env.ty t).kind = .agg pack fs) (hmem : (fld, j) ∈ fs.zipIdx)
    (hcs : callsShim P.env f k fld = true) :
    Reached P f k fld ∧
      (⟨.shim k t, j + 1, k, P.env.align t, t, [j], fld, P.layout t j⟩ : Pos) ∈ positions P :=
  ⟨⟨by have := h.1; omega, fun x hx =>
      h.2 x (reach_field_sub P.env f k t pack fs fld hkb hk (mem_zipIdx_fst fs 0 fld j hmem) hcs x hx)⟩,
    mem_positions_body P f k t pack fs fld j hkb hk hmem (by have := h.1; omega) hcs
      (h.2 _ (mem_reach_self P.env f k t))⟩

theorem aligned_of_not_misalignable {A n o a : Nat} (hA : A ∣ a) (hnm : ¬ Misalignable A n o) :
    n ∣ a + o :=
  Classical.byContradiction fun h => hnm ⟨a, hA, h⟩

theorem run_allEv (m : Mode) (cfg : Cfg) (P : Prog) (p : Ev → Prop)
    (hstep : ∀ op i, (op, i) ∈ P.src.zipIdx → AllEv p (srcStep m cfg P i op)) :
    AllEv p (run m cfg P) := by
  unfold run
  exact foldl_andThen_allEv p _ _ _ (fun q hq => hstep q.1 q.2 hq) (allEv_nil _ _)

theorem allEv_mono {p q : Ev → Prop} {o : Out} (h : AllEv p o) (hpq : ∀ e, p e → q e) :
    AllEv q o := fun e he => hpq e (h e he)

/-! ## Absence of UB from aligned shim entries -/

/-- Entering a reached shim at an aligned address produces no UB event, given coverage and
aligned temporaries. -/
theorem runShim_noUB_of_aligned (P : Prog) (cfg : Cfg) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) :
    ∀ fuel k t a n, Reached P fuel k t → P.env.align t ∣ a →
      AllEv (fun e => e.isUB = false) (runShim .ref cfg P.env P.layout fuel k t a n) := by
  intro fuel k t a n hr hal
  refine runShim_allEv .ref cfg P.env P.layout (fun e => e.isUB = false)
    (fun f k t a => Reached P f k t ∧ P.env.align t ∣ a) rfl
    (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) ?_ ?_ ?_ fuel k t a n ⟨hr, hal⟩
  · intro f k t a hinv _
    simp only [refStep, hinv.2, ↓reduceIte]
    exact allEv_nil _ _
  · intro f t a q hinv hk hnd
    exact ⟨reached_box hinv.1 hk hnd, Nat.dvd_refl _⟩
  · intro f k t a pack fs fld j hkb hinv hk hmem hcs
    obtain ⟨hr', hq⟩ := reached_field hinv.1 hkb hk hmem hcs
    refine ⟨fun hcr => ⟨fun _ => ⟨hr', ht _ hq hcr⟩, fun _ => rfl⟩, fun hcr => ⟨hr', ?_⟩⟩
    have hnm : ¬ Misalignable (P.env.align t) (P.env.align fld) (P.layout t j) := fun hm => by
      have := ha _ hq hm
      simp only [Pos.staged] at this
      rw [this] at hcr; cases hcr
    exact aligned_of_not_misalignable hinv.2 hnm

/-- A compiler operation in the source body produces no UB event, given aligned locals, coverage
and aligned temporaries. -/
theorem srcStep_comp_noUB (P : Prog) (cfg : Cfg) (hframe : FrameAligned P) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) (k : ShimKind) (p : Place) (i : Nat)
    (hmem : (Op.comp k p, i) ∈ P.src.zipIdx) :
    AllEv (fun e => e.isUB = false) (srcStep .ref cfg P i (.comp k p)) := by
  simp only [srcStep]
  split
  · rename_i A t0 u a hpl
    obtain ⟨o, hroot, hres, rfl, rfl, rfl⟩ := place_some hpl
    refine compStep_allEv _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (fun hcs => ?_)
    have hq := mem_srcPositions P k p i u o hmem hroot hres hcs
    have hr := reached_root P _ (mem_zipIdx_fst P.src 0 _ i hmem) k u (shimRoot_comp hpl hcs)
    refine ⟨fun hcr => ⟨fun _ => runShim_noUB_of_aligned P cfg ha ht _ _ _ _ _ hr (ht _ hq hcr),
      fun _ => rfl⟩, fun hcr => ?_⟩
    have hnm : ¬ Misalignable (P.env.align (P.locals.getD p.root 0)) (P.env.align u) o := fun hm => by
      have := ha _ hq hm
      simp only [Pos.staged] at this
      rw [this] at hcr; cases hcr
    exact runShim_noUB_of_aligned P cfg ha ht _ _ _ _ _ hr
      (aligned_of_not_misalignable (hframe p.root hroot) hnm)
  · exact allEv_nil _ _

/-- A raw client call that passes an aligned pointer to an existing shim produces no UB event,
given coverage and aligned temporaries; a raw call of a shim that does not exist produces no
event. -/
theorem srcStep_rawCall_noUB (P : Prog) (cfg : Cfg) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) (k : ShimKind) (t a i : Nat)
    (hmem : (Op.rawCall k t a, i) ∈ P.src.zipIdx)
    (hal : (Op.rawCall k t a).ptrAligned P.env = true) :
    AllEv (fun e => e.isUB = false) (srcStep .ref cfg P i (.rawCall k t a)) := by
  cases hex : shimExists P.env k t with
  | true =>
    exact runShim_noUB_of_aligned P cfg ha ht _ _ _ _ _
      (reached_root P _ (mem_zipIdx_fst P.src 0 _ i hmem) k t (shimRoot_rawCall P k t a hex))
      (ptrAligned_rawCall hal hex)
  | false =>
    simp only [srcStep, Prog.fuel, runShim_succ_missing _ _ _ _ _ _ _ _ _ hex]
    exact allEv_nil _ _

/-! ## Absence of UB under a covering policy -/

/-- Under a policy that checks op `0` of every existing shim of every type whose alignment is
not `1`, no shim run has a UB event. -/
theorem runShim_noUB_of_covered (cfg : Cfg) (env : Env) (L : Layout)
    (hcov : ∀ k t, t < env.length → env.align t ≠ 1 → shimExists env k t = true →
      cfg.instr (.shim k t) 0 = true) :
    ∀ fuel k t a n, AllEv (fun e => e.isUB = false) (runShim .ref cfg env L fuel k t a n) := by
  intro fuel k t a n
  refine runShim_allEv .ref cfg env L (fun e => e.isUB = false) (fun _ _ _ _ => True) rfl
    (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) ?_ (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨fun _ => ⟨fun _ => trivial, fun _ => rfl⟩, fun _ => trivial⟩)
    fuel k t a n trivial
  intro f k t a _ hex
  unfold refStep
  simp only
  split
  · exact allEv_nil _ _
  · rename_i hna
    have h1 : env.align t ≠ 1 := fun h => hna (by rw [h]; exact Nat.one_dvd a)
    simp only [hcov k t (lt_length_of_align_ne_one h1) h1 hex, ↓reduceIte]
    exact allEv_single _ rfl

/-! ## Absence of `stuck` -/

theorem runShim_noStuck (m : Mode) (P : Prog) (cfg : Cfg) (h1 : StagedSized P cfg) :
    ∀ fuel k t a n, Reached P fuel k t →
      AllEv (fun e => e.isStuck = false) (runShim m cfg P.env P.layout fuel k t a n) := by
  intro fuel k t a n hr
  refine runShim_allEv m cfg P.env P.layout (fun e => e.isStuck = false)
    (fun f k t _ => Reached P f k t) rfl
    (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) ?_ ?_ ?_ fuel k t a n hr
  · intro f k t a _ _
    unfold refStep
    cases m
    · exact allEv_nil _ _
    · simp only
      split
      · exact allEv_nil _ _
      · split <;> exact allEv_single _ rfl
  · intro f t a q hinv hk hnd
    exact reached_box hinv hk hnd
  · intro f k t a pack fs fld j hkb hinv hk hmem hcs
    obtain ⟨hr', hq⟩ := reached_field hinv hkb hk hmem hcs
    refine ⟨fun hcr => ⟨fun _ => hr', fun hsz => ?_⟩, fun _ => hr'⟩
    have := h1 _ hq hcr
    simp only at this
    rw [this] at hsz; cases hsz

/-! ## Staging: the staged reference run against the unstaged ideal run -/

/-- The relation between a staged reference-semantics outcome and an unstaged ideal-semantics
outcome: no UB event, equal observable traces, and the same continuation flag. -/
def StRel (o1 o2 : Out) : Prop := NoUB o1 ∧ obs o1.evs = obs o2.evs ∧ o1.ok = o2.ok

theorem obs_append (l1 l2 : List Ev) : obs (l1 ++ l2) = obs l1 ++ obs l2 := by
  simp [obs, List.filter_append]

theorem stRel_andThen (o1 o2 : Out) (g1 g2 : Unit → Out) (ho : StRel o1 o2)
    (hg : o1.ok = true → StRel (g1 ()) (g2 ())) : StRel (o1.andThen g1) (o2.andThen g2) := by
  simp only [StRel, Out.andThen, ← ho.2.2]
  split
  · rename_i hok
    have h := hg hok
    exact ⟨by intro e he; simp only [List.mem_append] at he; exact he.elim (ho.1 e) (h.1 e),
      by simp [obs_append, ho.2.1, h.2.1], h.2.2⟩
  · exact ⟨ho.1, ho.2.1, ho.2.2⟩

theorem stRel_same (o : Out) (h : NoUB o) : StRel o o := ⟨h, rfl, rfl⟩

theorem compStep_staging (call1 call2 : Nat → Nat → VName → Out) (env : Env) (fuel : Nat)
    (cfg : Cfg) (k : ShimKind) (b : BodyId) (i A t0 : Nat) (path : List Nat) (u a1 a2 : Nat)
    (n : VName)
    (h : callsShim env fuel k u = true →
      (cfg.crit k A t0 path = true →
        (env.ty u).sized = true ∧ StRel (call1 u (cfg.tmp b i) n) (call2 u a2 n)) ∧
      (cfg.crit k A t0 path = false → StRel (call1 u a1 n) (call2 u a2 n))) :
    StRel (compStep call1 env fuel cfg k b i A t0 path u a1 n)
      (compStep call2 env fuel cfg.unstaged k b i A t0 path u a2 n) := by
  unfold compStep
  simp only [Cfg.unstaged, critNone, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i hcs
    have h' := h hcs
    split
    · rename_i hcr
      obtain ⟨hsz, hrel⟩ := h'.1 hcr
      simp only [hsz, ↓reduceIte, Out.andThen]
      exact ⟨by
          intro e he
          simp only [List.cons_append, List.nil_append, List.mem_cons] at he
          exact he.elim (fun h => h ▸ rfl) (hrel.1 e),
        by simpa [obs] using hrel.2.1, hrel.2.2⟩
    · rename_i hcr
      exact h'.2 (by simpa using hcr)
  · exact stRel_same _ (by intro e he; cases he)

theorem runShim_staging (P : Prog) (cfg : Cfg) (hcov : CritCovers P cfg) (h1 : StagedSized P cfg)
    (h2 : StagedAddrBlind P cfg) (h3 : TempsAligned P cfg) :
    ∀ fuel k t a1 a2 n, Reached P fuel k t → P.env.align t ∣ a1 →
      (a1 = a2 ∨ (k = .dropGlue → AddrBlind P.env fuel t = true)) →
      StRel (runShim .ref cfg P.env P.layout fuel k t a1 n)
        (runShim .ideal cfg.unstaged P.env P.layout fuel k t a2 n)
  | 0, _, _, _, _, _, _, _, _ => by
    simp only [runShim]
    exact stRel_same _ (by intro e he; simp at he; subst he; rfl)
  | f + 1, k, t, a1, a2, n, hr, ha1, hrel => by
    simp only [runShim]
    by_cases hex : shimExists P.env k t = true
    · simp only [hex, ↓reduceIte]
      refine stRel_andThen _ _ _ _ (by
        simp only [refStep, ha1, ↓reduceIte]; exact stRel_same _ (by intro e he; cases he)) ?_
      intro _
      have IH := runShim_staging P cfg hcov h1 h2 h3 f
      have hagg : ∀ (k' : ShimKind) (pack : Option Nat) (fs : List Nat), k' = k →
          k' ≠ .boxFree → (P.env.ty t).kind = .agg pack fs →
          StRel (seqFields fs fun fld j =>
              compStep (fun u a' n' => runShim .ref cfg P.env P.layout f k' u a' n') P.env f cfg k'
                (.shim k' t) (j + 1) (P.env.align t) t [j] fld (a1 + P.layout t j) (n.child j))
            (seqFields fs fun fld j =>
              compStep (fun u a' n' => runShim .ideal cfg.unstaged P.env P.layout f k' u a' n')
                P.env f cfg.unstaged k' (.shim k' t) (j + 1) (P.env.align t) t [j] fld
                (a2 + P.layout t j) (n.child j)) := by
        intro k' pack fs hkk hkb hk
        subst hkk
        unfold seqFields
        refine foldl_andThen_rel StRel stRel_andThen _ _ fs.zipIdx _ _ (fun q hmem => ?_)
          (stRel_same _ (by intro e he; cases he))
        rcases q with ⟨fld, j⟩
        refine compStep_staging _ _ P.env f cfg k' _ _ _ _ _ fld _ _ _ (fun hcs => ?_)
        obtain ⟨hr', hq⟩ := reached_field hr hkb hk hmem hcs
        refine ⟨fun hcr => ⟨h1 _ hq hcr, ?_⟩, fun hcr => ?_⟩
        · exact IH k' fld _ _ _ hr' (h3 _ hq hcr)
            (Or.inr fun hkd => addrBlind_anti P.env f P.fuel fld (by have := hr.1; omega)
              (h2 _ hq hcr hkd))
        · have hnm : ¬ Misalignable (P.env.align t) (P.env.align fld) (P.layout t j) := fun hm => by
            have := hcov _ hq hm
            simp only [Pos.staged] at this
            rw [this] at hcr; cases hcr
          refine IH k' fld _ _ _ hr' (aligned_of_not_misalignable ha1 hnm) ?_
          rcases hrel with rfl | hab
          · exact Or.inl rfl
          · refine Or.inr fun hkd => ?_
            have h' := hab hkd
            simp only [AddrBlind, hk, List.all_eq_true] at h'
            exact h' fld (mem_zipIdx_fst fs 0 fld j hmem)
      cases k with
      | dropGlue =>
        cases hk : (P.env.ty t).kind with
        | scalar => exact stRel_same _ (by intro e he; cases he)
        | res o =>
          rcases hrel with rfl | hab
          · refine stRel_same _ ?_
            intro e he
            cases o
            · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append,
                List.mem_singleton] at he
              subst he; rfl
            · simp only [↓reduceIte, List.singleton_append, List.mem_cons, List.not_mem_nil,
                or_false] at he
              rcases he with rfl | rfl <;> rfl
          · have h' := hab rfl
            simp only [AddrBlind, hk, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
            subst h'
            exact stRel_same _ (by
              intro e he
              simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append,
                List.mem_singleton] at he
              subst he; rfl)
        | box q =>
          refine stRel_andThen _ _ _ _ ?_ (fun _ => stRel_same _ (by
            intro e he; simp at he; subst he; rfl))
          split
          · rename_i hnd
            exact IH .dropGlue q _ _ _ (reached_box hr hk hnd) (Nat.dvd_refl _) (Or.inl rfl)
          · exact stRel_same _ (by intro e he; cases he)
        | agg pack fs => exact hagg .dropGlue pack fs rfl (by decide) hk
      | boxFree => exact stRel_same _ (by intro e he; simp at he; subst he; rfl)
      | clone =>
        cases hk : (P.env.ty t).kind with
        | agg pack fs => exact hagg .clone pack fs rfl (by decide) hk
        | scalar => exact stRel_same _ (by intro e he; simp at he; subst he; rfl)
        | res _ => exact stRel_same _ (by intro e he; simp at he; subst he; rfl)
        | box _ => exact stRel_same _ (by intro e he; simp at he; subst he; rfl)
    · simp only [hex, Bool.false_eq_true, ↓reduceIte]
      exact stRel_same _ (by intro e he; cases he)

/-! ## Precision: the instrumented run against the uninstrumented run -/

/-- The relation between an instrumented and an uninstrumented outcome: events agree up to
relabelling UB events at checked positions as traps, and the continuation flags agree. -/
def PrRel (I : BodyId → Nat → Bool) (o1 o2 : Out) : Prop :=
  o1.evs = o2.evs.map (toTrap I) ∧ o1.ok = o2.ok

theorem prRel_andThen (I : BodyId → Nat → Bool) (o1 o2 : Out) (g1 g2 : Unit → Out)
    (ho : PrRel I o1 o2) (hg : o1.ok = true → PrRel I (g1 ()) (g2 ())) :
    PrRel I (o1.andThen g1) (o2.andThen g2) := by
  simp only [PrRel, Out.andThen, ← ho.2]
  split
  · rename_i hok
    have h := hg hok
    exact ⟨by simp [ho.1, h.1], h.2⟩
  · exact ho

theorem map_toTrap_of_noUB (I : BodyId → Nat → Bool) :
    ∀ l : List Ev, (∀ e, e ∈ l → e.isUB = false) → l.map (toTrap I) = l
  | [], _ => rfl
  | e :: l, h => by
    have he := h e (List.mem_cons_self ..)
    have hl := map_toTrap_of_noUB I l (fun e' he' => h e' (List.mem_cons_of_mem e he'))
    simp only [List.map_cons, hl]
    cases e <;> simp_all [toTrap, Ev.isUB]

theorem prRel_same (I : BodyId → Nat → Bool) (o : Out) (h : NoUB o) : PrRel I o o :=
  ⟨(map_toTrap_of_noUB I o.evs h).symm, rfl⟩

theorem refStep_precision (cfg : Cfg) (b : BodyId) (i n a : Nat) :
    PrRel cfg.instr (refStep .ref cfg b i n a)
      (refStep .ref { cfg with instr := fun _ _ => false } b i n a) := by
  unfold refStep
  simp only
  split
  · exact prRel_same _ _ (by intro e he; cases he)
  · split
    · rename_i hI
      exact ⟨by simp [toTrap, hI], rfl⟩
    · rename_i hI
      exact ⟨by simp [toTrap, hI], rfl⟩

theorem compStep_precision (call1 call2 : Nat → Nat → VName → Out) (env : Env) (fuel : Nat)
    (cfg : Cfg) (k : ShimKind) (b : BodyId) (i A t0 : Nat) (path : List Nat) (u a : Nat)
    (n : VName) (hcall : ∀ a', PrRel cfg.instr (call1 u a' n) (call2 u a' n)) :
    PrRel cfg.instr (compStep call1 env fuel cfg k b i A t0 path u a n)
      (compStep call2 env fuel { cfg with instr := fun _ _ => false } k b i A t0 path u a n) := by
  unfold compStep
  simp only
  split
  · split
    · split
      · simp only [Out.andThen, ↓reduceIte]
        exact ⟨by simp [(hcall _).1, toTrap], (hcall _).2⟩
      · exact prRel_same _ _ (by intro e he; simp at he; subst he; rfl)
    · exact hcall _
  · exact prRel_same _ _ (by intro e he; cases he)

theorem runShim_precision (cfg : Cfg) (env : Env) (L : Layout) :
    ∀ fuel k t a n, PrRel cfg.instr (runShim .ref cfg env L fuel k t a n)
      (runShim .ref { cfg with instr := fun _ _ => false } env L fuel k t a n)
  | 0, _, _, _, _ => by
    simp only [runShim]
    exact prRel_same _ _ (by intro e he; simp at he; subst he; rfl)
  | f + 1, k, t, a, n => by
    simp only [runShim]
    split
    · refine prRel_andThen _ _ _ _ _ (refStep_precision cfg _ _ _ _) (fun _ => ?_)
      have IH := runShim_precision cfg env L f
      have hagg : ∀ (k' : ShimKind) (fs : List Nat),
          PrRel cfg.instr (seqFields fs fun fld j =>
              compStep (fun u a' n' => runShim .ref cfg env L f k' u a' n') env f cfg k'
                (.shim k' t) (j + 1) (env.align t) t [j] fld (a + L t j) (n.child j))
            (seqFields fs fun fld j =>
              compStep (fun u a' n' => runShim .ref { cfg with instr := fun _ _ => false } env L f
                k' u a' n') env f { cfg with instr := fun _ _ => false } k' (.shim k' t) (j + 1)
                (env.align t) t [j] fld (a + L t j) (n.child j)) := by
        intro k' fs
        unfold seqFields
        refine foldl_andThen_rel (PrRel cfg.instr) (prRel_andThen cfg.instr) _ _ fs.zipIdx _ _
          (fun q _ => ?_) (prRel_same _ _ (by intro e he; cases he))
        exact compStep_precision _ _ env f cfg k' _ _ _ _ _ _ _ _ (fun a' => IH _ _ _ _)
      cases k with
      | dropGlue =>
        cases hk : (env.ty t).kind with
        | scalar => exact prRel_same _ _ (by intro e he; cases he)
        | res o =>
          refine prRel_same _ _ ?_
          intro e he
          cases o
          · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append,
              List.mem_singleton] at he
            subst he; rfl
          · simp only [↓reduceIte, List.singleton_append, List.mem_cons, List.not_mem_nil,
              or_false] at he
            rcases he with rfl | rfl <;> rfl
        | box q =>
          refine prRel_andThen _ _ _ _ _ ?_ (fun _ => prRel_same _ _ (by
            intro e he; simp at he; subst he; rfl))
          split
          · exact IH _ _ _ _
          · exact prRel_same _ _ (by intro e he; cases he)
        | agg pack fs => exact hagg .dropGlue fs
      | boxFree => exact prRel_same _ _ (by intro e he; simp at he; subst he; rfl)
      | clone =>
        cases hk : (env.ty t).kind with
        | agg pack fs => exact hagg .clone fs
        | scalar => exact prRel_same _ _ (by intro e he; simp at he; subst he; rfl)
        | res _ => exact prRel_same _ _ (by intro e he; simp at he; subst he; rfl)
        | box _ => exact prRel_same _ _ (by intro e he; simp at he; subst he; rfl)
    · exact prRel_same _ _ (by intro e he; cases he)

/-! ## Powers of two and the type-based guaranteed alignment -/

theorem align_of_ge {env : Env} {t : Nat} (h : env.length ≤ t) : env.align t = 1 := by
  have : env.ty t = default := by
    simp [Env.ty, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp only [Env.align, this]; rfl

theorem isPow2_one : IsPow2 1 := ⟨0, by decide, rfl⟩

theorem isPow2_align {env : Env} (hpow : PowTwoAligns env) (t : Nat) : IsPow2 (env.align t) := by
  cases Nat.lt_or_ge t env.length with
  | inl h => exact (hpow t h).1
  | inr h => rw [align_of_ge h]; exact isPow2_one

theorem pow2_dvd_of_le {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) (hle : a ≤ b) : a ∣ b := by
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, rfl⟩ := hb
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide)).mp hle)

theorem isPow2_min {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) : IsPow2 (min a b) := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.min_eq_left h]; exact ha
  | inr h => rw [Nat.min_eq_right h]; exact hb

theorem min_dvd_left_pow2 {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) : min a b ∣ a :=
  pow2_dvd_of_le (isPow2_min ha hb) ha (Nat.min_le_left a b)

theorem min_dvd_right_pow2 {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) : min a b ∣ b :=
  pow2_dvd_of_le (isPow2_min ha hb) hb (Nat.min_le_right a b)

theorem field?_some {env : Env} {t j f : Nat} (h : env.field? t j = some f) :
    t < env.length ∧ j < (env.fields t).length := by
  have hj : j < (env.fields t).length := by
    simp only [Env.field?, List.getElem?_eq_some_iff] at h
    obtain ⟨hj, _⟩ := h; exact hj
  refine ⟨?_, hj⟩
  cases hk : (env.ty t).kind with
  | agg pack fs => exact agg_lt_length hk
  | scalar => simp [Env.fields, hk] at hj
  | res _ => simp [Env.fields, hk] at hj
  | box _ => simp [Env.fields, hk] at hj

theorem isPow2_effAlign {env : Env} (hpow : PowTwoAligns env) {t j f : Nat}
    (h : env.field? t j = some f) : IsPow2 (effAlign env t j) := by
  have ht := (field?_some h).1
  unfold effAlign
  rw [h]
  cases hk : (env.ty t).kind with
  | agg pack fs =>
    cases pack with
    | none => exact isPow2_align hpow f
    | some n => exact isPow2_min ((hpow t ht).2 n fs hk) (isPow2_align hpow f)
  | scalar => simp [Env.field?, Env.fields, hk] at h
  | res _ => simp [Env.field?, Env.fields, hk] at h
  | box _ => simp [Env.field?, Env.fields, hk] at h

theorem typeGA_props (env : Env) (hpow : PowTwoAligns env) :
    ∀ (path : List Nat) (t g : Nat), IsPow2 g →
      IsPow2 (typeGA env t path g) ∧ typeGA env t path g ∣ g ∧
      ∀ s, s ∈ pathSteps env t path → typeGA env t path g ∣ effAlign env s.1 s.2
  | [], _, g, hg => ⟨hg, Nat.dvd_refl g, fun _ hs => by simp [pathSteps] at hs⟩
  | j :: rest, t, g, hg => by
    cases hf : env.field? t j with
    | none =>
      simp only [typeGA, pathSteps, hf]
      exact ⟨hg, Nat.dvd_refl g, fun _ hs => by cases hs⟩
    | some f =>
      simp only [typeGA, pathSteps, hf]
      have he := isPow2_effAlign hpow hf
      have IH := typeGA_props env hpow rest f (min g (effAlign env t j)) (isPow2_min hg he)
      refine ⟨IH.1, Nat.dvd_trans IH.2.1 (min_dvd_left_pow2 hg he), fun s hs => ?_⟩
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact Nat.dvd_trans IH.2.1 (min_dvd_right_pow2 hg he)
      · exact IH.2.2 s hs

theorem typeGA_cases (env : Env) :
    ∀ (path : List Nat) (t g : Nat),
      typeGA env t path g = g ∨
      ∃ s, s ∈ pathSteps env t path ∧ typeGA env t path g = effAlign env s.1 s.2
  | [], _, _ => Or.inl rfl
  | j :: rest, t, g => by
    cases hf : env.field? t j with
    | none => left; simp [typeGA, hf]
    | some f =>
      simp only [typeGA, pathSteps, hf]
      rcases typeGA_cases env rest f (min g (effAlign env t j)) with h | ⟨s, hs, h⟩
      · rw [h]
        cases Nat.le_total g (effAlign env t j) with
        | inl hle => exact Or.inl (Nat.min_eq_left hle)
        | inr hle => exact Or.inr ⟨(t, j), List.mem_cons_self .., Nat.min_eq_right hle⟩
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, h⟩

theorem pathSteps_valid (env : Env) :
    ∀ (path : List Nat) (t : Nat) (s : Nat × Nat), s ∈ pathSteps env t path →
      s.1 < env.length ∧ s.2 < (env.fields s.1).length
  | [], _, _, hs => by simp [pathSteps] at hs
  | j :: rest, t, s, hs => by
    cases hf : env.field? t j with
    | none => simp [pathSteps, hf] at hs
    | some f =>
      simp only [pathSteps, hf, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact field?_some hf
      · exact pathSteps_valid env rest f s hs

theorem resolve_typeAt (env : Env) (L : Layout) :
    ∀ (path : List Nat) (t u o : Nat), resolve env L t path = some (u, o) →
      typeAt env t path = some u
  | [], t, u, o, h => by
    simp only [resolve, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; rfl
  | j :: rest, t, u, o, h => by
    cases hf : env.field? t j with
    | none => simp [resolve, hf] at h
    | some f =>
      simp only [resolve, hf] at h
      simp only [typeAt, hf]
      cases hr : resolve env L f rest with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨u', o'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact resolve_typeAt env L rest f u' o' hr

theorem resolve_dvd (env : Env) (L : Layout) (d : Nat) :
    ∀ (path : List Nat) (t u o : Nat), resolve env L t path = some (u, o) →
      (∀ s, s ∈ pathSteps env t path → d ∣ L s.1 s.2) → d ∣ o
  | [], t, u, o, h, _ => by
    simp only [resolve, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact Nat.dvd_zero d
  | j :: rest, t, u, o, h, hd => by
    cases hf : env.field? t j with
    | none => simp [resolve, hf] at h
    | some f =>
      simp only [resolve, hf] at h
      cases hr : resolve env L f rest with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨u', o'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have hsteps : pathSteps env t (j :: rest) = (t, j) :: pathSteps env f rest := by
          simp [pathSteps, hf]
        refine Nat.dvd_add (hd (t, j) (by rw [hsteps]; exact List.mem_cons_self ..)) ?_
        exact resolve_dvd env L d rest f u' o' hr
          (fun s hs => hd s (by rw [hsteps]; exact List.mem_cons_of_mem _ hs))

/-- Resolving a path under a layout that is `c` at one step `x` and `0` elsewhere. -/
theorem resolve_indicator (env : Env) (x : Nat × Nat) (c : Nat) :
    ∀ (path : List Nat) (t u : Nat), (pathSteps env t path).Nodup → typeAt env t path = some u →
      resolve env (fun t' j' => if (t', j') = x then c else 0) t path =
        some (u, if x ∈ pathSteps env t path then c else 0)
  | [], t, u, _, h => by
    simp only [typeAt, Option.some.injEq] at h
    subst h
    simp [resolve, pathSteps]
  | j :: rest, t, u, hnd, h => by
    cases hf : env.field? t j with
    | none => simp [typeAt, hf] at h
    | some f =>
      simp only [typeAt, hf] at h
      simp only [pathSteps, hf] at hnd ⊢
      rw [List.nodup_cons] at hnd
      simp only [resolve, hf, resolve_indicator env x c rest f u hnd.2 h, Option.map_some,
        Option.some.injEq, Prod.mk.injEq, true_and, List.mem_cons]
      by_cases hx : (t, j) = x
      · subst hx
        simp [hnd.1]
      · have hx' : ¬ x = (t, j) := fun h => hx h.symm
        simp [hx, hx']

/-! ## Positions resolve to their places -/

theorem pos_resolve (P : Prog) (q : Pos) (hq : q ∈ positions P) :
    q.A = P.env.align q.t0 ∧ resolve P.env P.layout q.t0 q.path = some (q.u, q.o) := by
  simp only [positions, List.mem_append] at hq
  rcases hq with hq | hq
  · simp only [srcPositions, List.mem_filterMap] at hq
    obtain ⟨⟨op, i⟩, _, hop⟩ := hq
    cases op with
    | comp k p =>
      simp only at hop
      split at hop
      · split at hop
        · rename_i u o hres
          split at hop
          · simp only [Option.some.injEq] at hop
            subst hop
            exact ⟨rfl, hres⟩
          · cases hop
        · cases hop
      · cases hop
    | moveOut _ => cases hop
    | readUnaligned _ _ => cases hop
    | rawRef _ _ => cases hop
    | rawCall _ _ _ => cases hop
  · simp only [shimPositions, List.mem_flatMap] at hq
    obtain ⟨⟨k, t⟩, _, hq⟩ := hq
    have key : ∀ q', q' ∈ (P.env.fields t).zipIdx.filterMap (fun q =>
        if callsShim P.env P.fuel k q.1 then
          some (⟨.shim k t, q.2 + 1, k, P.env.align t, t, [q.2], q.1, P.layout t q.2⟩ : Pos)
        else none) →
        q'.A = P.env.align q'.t0 ∧ resolve P.env P.layout q'.t0 q'.path = some (q'.u, q'.o) := by
      intro q' hq'
      simp only [List.mem_filterMap] at hq'
      obtain ⟨⟨fld, j⟩, hmem, hq'⟩ := hq'
      split at hq'
      · simp only [Option.some.injEq] at hq'
        subst hq'
        have hf : P.env.field? t j = some fld := List.mem_zipIdx_iff_getElem?.mp hmem
        exact ⟨rfl, by simp [resolve, hf]⟩
      · cases hq'
    cases k with
    | boxFree => simp [bodyPositions] at hq
    | dropGlue => exact key q hq
    | clone => exact key q hq

/-! ## Safe source bodies -/

/-- A source body without raw-pointer operations passes no raw pointer to a shim and creates no
user reference, whatever the instrumentation policy. -/
theorem clientPtrsAligned_and_srcRefsInstrumented_of_safeSrc (P : Prog) (cfg : Cfg)
    (hs : SafeSrc P) : ClientPtrsAligned P ∧ SrcRefsInstrumented P cfg := by
  refine ⟨fun op hop => ?_, fun q hq hr => ?_⟩
  · have := hs op hop
    cases op <;> simp_all [Op.isSafe, Op.ptrAligned]
  · have := hs q.1 (mem_zipIdx_fst P.src 0 q.1 q.2 hq)
    cases h : q.1 <;> simp_all [Op.isSafe, Op.isRawRef]

/-! ## Decreasing field ids imply no repeated step -/

theorem pathSteps_fst_le (env : Env) (h : FieldIdsDecreasing env) :
    ∀ (path : List Nat) (t : Nat) (s : Nat × Nat), s ∈ pathSteps env t path → s.1 ≤ t
  | [], _, _, hs => by simp [pathSteps] at hs
  | j :: rest, t, s, hs => by
    cases hf : env.field? t j with
    | none => simp [pathSteps, hf] at hs
    | some f =>
      simp only [pathSteps, hf, List.mem_cons] at hs
      have hft : f < t := h t (field?_some hf).1 f (List.mem_of_getElem? hf)
      rcases hs with rfl | hs
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (pathSteps_fst_le env h rest f s hs) hft)

/-- When field type ids decrease, no path repeats a projection step. -/
theorem noRepeatStep_of_fieldIdsDecreasing (env : Env) (h : FieldIdsDecreasing env) :
    ∀ (t0 : Nat) (path : List Nat), NoRepeatStep env t0 path
  | _, [] => by simp [NoRepeatStep, pathSteps]
  | t, j :: rest => by
    unfold NoRepeatStep
    cases hf : env.field? t j with
    | none => simp [pathSteps, hf]
    | some f =>
      simp only [pathSteps, hf, List.nodup_cons]
      have hft : f < t := h t (field?_some hf).1 f (List.mem_of_getElem? hf)
      refine ⟨fun hmem => ?_, noRepeatStep_of_fieldIdsDecreasing env h f rest⟩
      have := pathSteps_fst_le env h rest f (t, j) hmem
      simp only at this
      omega

end Toy.Packed
