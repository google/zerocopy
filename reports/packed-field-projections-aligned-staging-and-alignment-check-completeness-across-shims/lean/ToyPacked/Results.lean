import ToyPacked.Lemmas

/-!
# Main results

Concrete counterexamples, non-vacuity witnesses and positive controls for these statements are in
`ToyPacked/Counterexamples.lean`; the lemmas used in the proofs are in `ToyPacked/Lemmas.lean`.
These are statements about the toy model; they neither establish nor refute the corresponding
claims about Rust, rustc or Miri. Model–system relation: none proved.
-/

namespace Toy.Packed

/-! ## Aligned staging (result `staging`) -/

/-- Aligned staging is sound and preserves observable behaviour. For a program whose locals are
placed at aligned addresses (`FrameAligned`) and whose source body has no raw-pointer operations
(`SafeSrc`), if every compiler-operation position (of the source body and of the shims the
program may enter) with a misalignable place is staged (`CritCovers`), every staged value is
sized (H1), no destructor reachable from a staged drop through inline sub-values observes its
address (H2), and every staging temporary is aligned for its type (H3), then the staged
program's reference-semantics run has no UB event and its observable trace equals the
ideal-semantics trace of the unstaged program. The instrumentation policy `cfg.instr` is
arbitrary. -/
theorem staged_noUB_and_obs_eq_ideal_of_frameAligned_safeSrc_covers_sized_addrBlind_alignedTemps
    (P : Prog) (cfg : Cfg)
    (hframe : FrameAligned P) (hsafe : SafeSrc P) (hcov : CritCovers P cfg)
    (h1 : StagedSized P cfg) (h2 : StagedAddrBlind P cfg) (h3 : TempsAligned P cfg) :
    NoUB (run .ref cfg P) ∧ obs (run .ref cfg P).evs = obs (run .ideal cfg.unstaged P).evs := by
  have h : StRel (run .ref cfg P) (run .ideal cfg.unstaged P) := by
    unfold run
    refine foldl_andThen_rel StRel stRel_andThen _ _ P.src.zipIdx _ _ (fun q hq => ?_)
      (stRel_same _ (by intro e he; cases he))
    rcases q with ⟨op, i⟩
    have hop := mem_zipIdx_fst P.src 0 op i hq
    cases op with
    | comp k p =>
      simp only [srcStep]
      cases hpl : P.place p with
      | none => exact stRel_same _ (by intro e he; cases he)
      | some r =>
        obtain ⟨A, t0, u, a⟩ := r
        obtain ⟨o, hroot, hres, rfl, rfl, rfl⟩ := place_some hpl
        refine compStep_staging _ _ P.env P.fuel cfg k _ _ _ _ _ u _ _ _ (fun hcs => ?_)
        have hq' := mem_srcPositions P k p i u o hq hroot hres hcs
        have hr := reached_root P _ hop k u (shimRoot_comp hpl hcs)
        refine ⟨fun hcr => ⟨h1 _ hq' hcr, ?_⟩, fun hcr => ?_⟩
        · exact runShim_staging P cfg hcov h1 h2 h3 _ _ _ _ _ _ hr (h3 _ hq' hcr)
            (Or.inr (h2 _ hq' hcr))
        · have hnm : ¬ Misalignable (P.env.align (P.locals.getD p.root 0)) (P.env.align u) o :=
            fun hm => by
              have := hcov _ hq' hm
              simp only [Pos.staged] at this
              rw [this] at hcr; cases hcr
          exact runShim_staging P cfg hcov h1 h2 h3 _ _ _ _ _ _ hr
            (aligned_of_not_misalignable (hframe p.root hroot) hnm) (Or.inl rfl)
    | moveOut _ => exact stRel_same _ (by intro e he; cases he)
    | readUnaligned _ _ => exact stRel_same _ (by intro e he; cases he)
    | rawRef _ _ => have := hsafe _ hop; simp [Op.isSafe] at this
    | rawCall _ _ _ => have := hsafe _ hop; simp [Op.isSafe] at this
  exact ⟨h.1, h.2.1⟩

/-! ## Staging criteria -/

/-- The type-based criterion is sound. If all alignments and `packed(n)` parameters are powers of
two (`PowTwoAligns`), the layout respects packing (`RespectsPacking`), and the path resolves to a
place of type `u` at offset `o`, then a place whose type alignment divides its type-based
guaranteed alignment `typeGA` (computed along the whole path) cannot be misaligned. -/
theorem not_misalignable_of_powTwo_respectsPacking_dvd_typeGA (env : Env) (L : Layout)
    (hpow : PowTwoAligns env) (hpack : RespectsPacking env L)
    (t0 : Nat) (path : List Nat) (u o : Nat) (hres : resolve env L t0 path = some (u, o))
    (hdvd : env.align u ∣ typeGA env t0 path (env.align t0)) :
    ¬ Misalignable (env.align t0) (env.align u) o := by
  have hA := isPow2_align hpow t0
  have hp := typeGA_props env hpow path t0 (env.align t0) hA
  have ho : typeGA env t0 path (env.align t0) ∣ o := by
    refine resolve_dvd env L _ path t0 u o hres (fun s hs => ?_)
    have hv := pathSteps_valid env path t0 s hs
    exact Nat.dvd_trans (hp.2.2 s hs) (hpack s.1 hv.1 s.2 hv.2)
  rw [misalignable_iff_not_dvd_gcd]
  exact fun h => h (Nat.dvd_gcd (Nat.dvd_trans hdvd hp.2.1) (Nat.dvd_trans hdvd ho))

/-- Staging with the type-based criterion covers every misalignable compiler-operation position:
if all alignments and `packed(n)` parameters of the environment are powers of two and the layout
respects packing, then `critType` stages every position whose place is misalignable. -/
theorem critCovers_critType_of_powTwo_respectsPacking (P : Prog) (tmp : BodyId → Nat → Nat)
    (I : BodyId → Nat → Bool) (hpow : PowTwoAligns P.env) (hpack : RespectsPacking P.env P.layout) :
    CritCovers P ⟨critType P.env, tmp, I⟩ := by
  intro q hq hmis
  obtain ⟨hA, hres⟩ := pos_resolve P q hq
  simp only [Pos.staged, critType, resolve_typeAt P.env P.layout q.path q.t0 q.u q.o hres]
  rw [hA] at hmis
  cases hd : decide (P.env.align q.u ∣ typeGA P.env q.t0 q.path q.A) with
  | false => rfl
  | true =>
    rw [hA] at hd
    exact absurd hmis (not_misalignable_of_powTwo_respectsPacking_dvd_typeGA P.env P.layout hpow
      hpack q.t0 q.path q.u q.o hres (of_decide_eq_true hd))

/-- The type-based criterion is exact among layouts that respect packing. If all alignments and
`packed(n)` parameters of the environment are powers of two (`PowTwoAligns`), the path from `t0`
leads to a place of type `u` (`typeAt`), and the path takes no projection step `(t, j)` twice
(`NoRepeatStep`), then some packing-respecting layout makes the place misalignable iff the
place's type alignment does not divide `typeGA`. -/
theorem exists_respectsPacking_layout_misalignable_iff_not_dvd_typeGA_of_noRepeatStep_powTwo
    (env : Env) (hpow : PowTwoAligns env)
    (t0 : Nat) (path : List Nat) (u : Nat) (hty : typeAt env t0 path = some u)
    (hsteps : NoRepeatStep env t0 path) :
    (∃ L : Layout, RespectsPacking env L ∧ ∃ o, resolve env L t0 path = some (u, o) ∧
        Misalignable (env.align t0) (env.align u) o) ↔
      ¬ env.align u ∣ typeGA env t0 path (env.align t0) := by
  constructor
  · rintro ⟨L, hpack, o, hres, hmis⟩ hdvd
    exact not_misalignable_of_powTwo_respectsPacking_dvd_typeGA env L hpow hpack t0 path u o hres
      hdvd hmis
  · intro hnd
    have hA := isPow2_align hpow t0
    have hp := typeGA_props env hpow path t0 (env.align t0) hA
    rcases typeGA_cases env path t0 (env.align t0) with hg | ⟨s, hs, hg⟩
    · refine ⟨fun t' j' => if (t', j') = (0, 0) then 0 else 0, fun t _ j _ => ?_, 0, ?_, ?_⟩
      · dsimp only
        split <;> exact Nat.dvd_zero _
      · rw [resolve_indicator env (0, 0) 0 path t0 u hsteps hty]
        split <;> rfl
      · rw [misalignable_iff_not_dvd_gcd, Nat.gcd_zero_right]
        rwa [hg] at hnd
    · refine ⟨fun t' j' => if (t', j') = s then typeGA env t0 path (env.align t0) else 0,
        fun t _ j _ => ?_, typeGA env t0 path (env.align t0), ?_, ?_⟩
      · dsimp only
        split
        · rename_i h
          rw [hg]
          subst h
          exact Nat.dvd_refl _
        · exact Nat.dvd_zero _
      · rw [resolve_indicator env s _ path t0 u hsteps hty]
        simp [hs]
      · rw [misalignable_iff_not_dvd_gcd, Nat.gcd_eq_right hp.2.1]
        exact hnd

/-! ## Instrumentation completeness (result `completeness`) -/

/-- Completeness of an instrumentation policy over the class of all programs over a fixed
environment and layout, with a fixed staging criterion and temporaries, where the policy `I` is
fixed before the program (programs may contain unsafe client calls that pass arbitrary raw
pointers to any shim, user reference creations at any source position, and locals at any
address): every run produced by `run` in the reference semantics has no UB event iff the policy
covers op `0` of every existing shim of every type whose alignment is not `1`, and, when such a
type exists, every source position. -/
theorem noUB_forall_progs_iff_alignRelevantCovered (env : Env) (L : Layout) (crit : Crit)
    (tmp : BodyId → Nat → Nat) (I : BodyId → Nat → Bool) :
    (∀ P : Prog, P.env = env → P.layout = L → NoUB (run .ref ⟨crit, tmp, I⟩ P)) ↔
      AlignRelevantCovered env I := by
  constructor
  · intro h
    refine ⟨fun k t ht h1 hex => ?_, fun ⟨t, ht, h1⟩ i => ?_⟩
    · cases hI : I (.shim k t) 0 with
      | true => rfl
      | false =>
        exfalso
        have hn : ¬ env.align t ∣ 1 := fun hd => h1 (Nat.dvd_one.mp hd)
        have hrun : (run .ref ⟨crit, tmp, I⟩ ⟨env, L, [], [], [.rawCall k t 1]⟩).evs =
            [.ub (.shim k t) 0] := by
          simp [run, srcStep, Prog.fuel, runShim, hex, refStep, hn, hI, Out.andThen]
        have := h ⟨env, L, [], [], [.rawCall k t 1]⟩ rfl rfl (.ub (.shim k t) 0)
          (by rw [hrun]; exact List.mem_cons_self ..)
        simp [Ev.isUB] at this
    · cases hI : I .src i with
      | true => rfl
      | false =>
        exfalso
        have hn : ¬ env.align t ∣ 1 := fun hd => h1 (Nat.dvd_one.mp hd)
        let P : Prog := ⟨env, L, [], [], List.replicate i (.readUnaligned 0 0) ++ [.rawRef t 1]⟩
        have hpre : ∀ l : List (Op × Nat), (∀ x, x ∈ l → x.1 = .readUnaligned 0 0) →
            l.foldl (fun (acc : Out) (p : Op × Nat) =>
                acc.andThen fun _ => srcStep .ref ⟨crit, tmp, I⟩ P p.2 p.1)
              (⟨[], true⟩ : Out) = (⟨[], true⟩ : Out) := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons x l ih =>
            intro hl
            simp only [List.foldl_cons]
            have hx := hl x (List.mem_cons_self ..)
            rcases x with ⟨op, j⟩
            simp only at hx
            subst hx
            simp only [srcStep, Out.andThen, ↓reduceIte, List.append_nil]
            exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        have hrun : (run .ref ⟨crit, tmp, I⟩ P).evs = [.ub .src i] := by
          simp only [run, P, List.zipIdx_append, List.foldl_append]
          rw [hpre _ (fun x hx => List.eq_of_mem_replicate (mem_zipIdx_fst _ 0 x.1 x.2 hx))]
          simp [srcStep, refStep, hn, hI, Out.andThen]
        have := h P rfl rfl (.ub .src i) (by rw [hrun]; exact List.mem_cons_self ..)
        simp [Ev.isUB] at this
  · rintro hcov P rfl rfl
    refine run_allEv .ref _ P _ (fun op i _ => ?_)
    cases op with
    | comp k p =>
      simp only [srcStep]
      split
      · exact compStep_allEv _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (fun _ =>
          ⟨fun _ => ⟨fun _ => runShim_noUB_of_covered _ _ _ hcov.1 _ _ _ _ _, fun _ => rfl⟩,
            fun _ => runShim_noUB_of_covered _ _ _ hcov.1 _ _ _ _ _⟩)
      · exact allEv_nil _ _
    | moveOut _ => exact allEv_nil _ _
    | readUnaligned _ _ => exact allEv_nil _ _
    | rawRef t a =>
      simp only [srcStep, refStep]
      split
      · exact allEv_nil _ _
      · rename_i hna
        have h1 : P.env.align t ≠ 1 := fun h => hna (by rw [h]; exact Nat.one_dvd a)
        simp only [hcov.2 ⟨t, lt_length_of_align_ne_one h1, h1⟩ i, ↓reduceIte]
        exact allEv_single _ rfl
    | rawCall k t a => exact runShim_noUB_of_covered _ _ _ hcov.1 _ _ _ _ _

/-- Precision: for every program and configuration, the instrumented reference-semantics run
equals the uninstrumented one with UB events at checked positions relabelled as traps. So a check
traps only at a checked position where the uninstrumented run has a UB event (a misaligned
reference creation), never at an aligned reference creation. -/
theorem run_eq_uninstrumented_map_toTrap (P : Prog) (cfg : Cfg) :
    (run .ref cfg P).evs = (run .ref { cfg with instr := fun _ _ => false } P).evs.map
      (toTrap cfg.instr) := by
  have h : PrRel cfg.instr (run .ref cfg P) (run .ref { cfg with instr := fun _ _ => false } P) := by
    unfold run
    refine foldl_andThen_rel (PrRel cfg.instr) (prRel_andThen cfg.instr) _ _ P.src.zipIdx _ _
      (fun q _ => ?_) (prRel_same _ _ (by intro e he; cases he))
    rcases q with ⟨op, i⟩
    cases op with
    | comp k p =>
      simp only [srcStep]
      split
      · exact compStep_precision _ _ _ _ cfg k _ _ _ _ _ _ _ _
          (fun a' => runShim_precision cfg _ _ _ _ _ _ _)
      · exact prRel_same _ _ (by intro e he; cases he)
    | moveOut _ => exact prRel_same _ _ (by intro e he; cases he)
    | readUnaligned _ _ => exact prRel_same _ _ (by intro e he; cases he)
    | rawRef t a => exact refStep_precision cfg _ _ _ _
    | rawCall k t a => exact runShim_precision cfg _ _ _ _ _ _ _
  exact h.1

/-! ## Conditional sufficiency without shim instrumentation (result `sufficiency`) -/

/-- For a program whose locals are aligned (`FrameAligned`), if (a) every compiler-operation
position with a misalignable place is staged (`CritCovers`) into a temporary aligned for the
staged type (`TempsAligned`), (b) every raw pointer that unsafe client code passes to an existing
shim is aligned for the shim's type (`ClientPtrsAligned`), and (c) every user-written reference
creation in the source body is instrumented (`SrcRefsInstrumented`), then the reference-semantics
run has no UB event, whatever checks the shims have (none required). The run may still end with
`trap`, `stuck` or `outOfFuel`. -/
theorem noUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned_srcRefsInstrumented
    (P : Prog) (cfg : Cfg) (hframe : FrameAligned P) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) (hb : ClientPtrsAligned P) (hc : SrcRefsInstrumented P cfg) :
    NoUB (run .ref cfg P) := by
  refine run_allEv .ref cfg P _ (fun op i hmem => ?_)
  have hop := mem_zipIdx_fst P.src 0 op i hmem
  cases op with
  | comp k p => exact srcStep_comp_noUB P cfg hframe ha ht k p i hmem
  | moveOut _ => exact allEv_nil _ _
  | readUnaligned _ _ => exact allEv_nil _ _
  | rawRef t a =>
    simp only [srcStep, refStep, hc _ hmem rfl]
    split
    · exact allEv_nil _ _
    · exact allEv_single _ rfl
  | rawCall k t a =>
    exact srcStep_rawCall_noUB P cfg ha ht k t a i hmem (hb _ hop)

/-- Under premises (a) and (b) alone, for a program whose locals are aligned, no UB event occurs
inside a shim. The run may still have a UB event in the source body, and it may still end with
`trap`, `stuck` or `outOfFuel`. -/
theorem noShimUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned
    (P : Prog) (cfg : Cfg) (hframe : FrameAligned P) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) (hb : ClientPtrsAligned P) :
    NoShimUB (run .ref cfg P) := by
  have hw : ∀ e : Ev, e.isUB = false → e.isShimUB = false := by
    intro e h; cases e <;> simp_all [Ev.isUB, Ev.isShimUB]
  refine run_allEv .ref cfg P _ (fun op i hmem => ?_)
  have hop := mem_zipIdx_fst P.src 0 op i hmem
  cases op with
  | comp k p => exact allEv_mono (srcStep_comp_noUB P cfg hframe ha ht k p i hmem) hw
  | moveOut _ => exact allEv_nil _ _
  | readUnaligned _ _ => exact allEv_nil _ _
  | rawRef t a =>
    simp only [srcStep, refStep]
    split
    · exact allEv_nil _ _
    · split <;> exact allEv_single _ rfl
  | rawCall k t a =>
    exact allEv_mono (srcStep_rawCall_noUB P cfg ha ht k t a i hmem (hb _ hop)) hw

/-! ## Unsized staged values (result `no-stuck`) -/

/-- If every staged position of a program (of its source body and of the shims it may enter)
has a sized type (H1, `StagedSized`), then no run of the program, in either semantics, has a
`stuck` event. -/
theorem noStuck_of_stagedSized (m : Mode) (P : Prog) (cfg : Cfg) (h1 : StagedSized P cfg) :
    NoStuck (run m cfg P) := by
  refine run_allEv m cfg P _ (fun op i hmem => ?_)
  have hop := mem_zipIdx_fst P.src 0 op i hmem
  cases op with
  | comp k p =>
    simp only [srcStep]
    cases hpl : P.place p with
    | none => exact allEv_nil _ _
    | some r =>
      obtain ⟨A, t0, u, a⟩ := r
      obtain ⟨o, hroot, hres, rfl, rfl, rfl⟩ := place_some hpl
      refine compStep_allEv _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (fun hcs => ?_)
      have hq := mem_srcPositions P k p i u o hmem hroot hres hcs
      have hr := reached_root P _ hop k u (shimRoot_comp hpl hcs)
      refine ⟨fun hcr => ⟨fun _ => runShim_noStuck m P cfg h1 _ _ _ _ _ hr, fun hsz => ?_⟩,
        fun _ => runShim_noStuck m P cfg h1 _ _ _ _ _ hr⟩
      have := h1 _ hq hcr
      simp only at this
      rw [this] at hsz; cases hsz
  | moveOut _ => exact allEv_nil _ _
  | readUnaligned _ _ => exact allEv_nil _ _
  | rawRef t a =>
    simp only [srcStep, refStep]
    cases m
    · exact allEv_nil _ _
    · simp only
      split
      · exact allEv_nil _ _
      · split <;> exact allEv_single _ rfl
  | rawCall k t a =>
    cases hex : shimExists P.env k t with
    | true =>
      exact runShim_noStuck m P cfg h1 _ _ _ _ _
        (reached_root P _ hop k t (shimRoot_rawCall P k t a hex))
    | false =>
      simp only [srcStep, Prog.fuel, runShim_succ_missing _ _ _ _ _ _ _ _ _ hex]
      exact allEv_nil _ _

end Toy.Packed
