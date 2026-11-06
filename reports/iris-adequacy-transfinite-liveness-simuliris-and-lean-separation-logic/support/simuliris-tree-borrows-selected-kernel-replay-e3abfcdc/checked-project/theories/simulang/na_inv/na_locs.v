From stdpp Require Import prelude gmap.
From simuliris.simulation Require Import language lifting.
From simuliris.simulang Require Import class_instances.
From simuliris.simulang Require Export lang notation.

(** * Pure reasoning for exploiting UB of dataraces

This file contains the pure reasoning that is necessary to exploit UB
of non-atomic accesses. The main definition is [na_locs_wf], which
keeps track of the alternaive executions which are used to justify the
optimizations. *)

(* TODO: move these two lemmas somewhere else? *)
Lemma safe_reach_store P_s (l_s : loc) (v' : val) σ o Φ:
  o ≠ Na2Ord →
  safe_reach P_s (Val #()) (state_upd_heap <[l_s:=(RSt 0, v')]> σ) Φ →
  safe_reach P_s (Store o #l_s v') σ Φ.
Proof.
  move => ??.
  apply: safe_reach_safe_implies.
  move => [?[?[[<-]?]]]; simplify_eq.
  destruct o => //.
  - by apply: safe_reach_base_step; [by econstructor|].
  - apply: safe_reach_base_step; [by econstructor|].
    apply: safe_reach_base_step; [econstructor; by rewrite lookup_insert_eq|].
    destruct σ => /=. by rewrite insert_insert_eq.
Qed.

Lemma safe_reach_load P_s (l_s : loc) (v' : val) σ o Φ n:
  o ≠ Na2Ord →
  σ.(heap) !! l_s = Some (RSt n, v') →
  safe_reach P_s (Val v') σ Φ →
  safe_reach P_s (Load o #l_s) σ Φ.
Proof.
  move => ???.
  destruct o => //.
  - by apply: safe_reach_base_step; [by econstructor|].
  - apply: safe_reach_base_step; [by econstructor|].
    apply: safe_reach_base_step; [econstructor; by rewrite lookup_insert_eq|].
    destruct σ => /=. by rewrite insert_insert_eq insert_id.
Qed.

Inductive na_locs_state :=
| NaExcl | NaRead (q : Qp).

Definition is_not_naexcl (ns : option (loc * na_locs_state)) : Prop :=
  (if ns is Some (_, NaExcl) then False else True).

Global Instance na_locs_state_eq_dec : EqDecision na_locs_state.
Proof. solve_decision. Qed.

Global Instance is_not_naexcl_dec ns : Decision (is_not_naexcl ns).
Proof. destruct ns as [[?[]]|] => /=; apply _. Qed.

Definition combine_na_locs (a b : option (option na_locs_state)) : option (option na_locs_state) :=
  match a, b with
  | None, _ => None
  | Some None, _ => b
  | Some (Some NaExcl), Some None => Some (Some NaExcl)
  | Some (Some NaExcl), Some _ => None
  | Some (Some (NaRead q1)), Some None => Some (Some (NaRead q1))
  | Some (Some (NaRead q1)), Some (Some NaExcl) => None
  | Some (Some (NaRead q1)), Some (Some (NaRead q2)) => Some (Some (NaRead (q1 + q2)))
  | _, None => None
  end.
Arguments combine_na_locs : simpl nomatch.

Fixpoint combine_na_locs_list (cols : list (gmap loc (loc * na_locs_state))) (l_s : loc) : option (option na_locs_state) :=
  match cols with
  | [] => Some None
  | col::cols =>
    combine_na_locs (Some (snd <$> (col !! l_s))) (combine_na_locs_list cols l_s)
  end.

Section combine_na_locs.
  Global Instance combine_na_locs_commute : Comm (=) combine_na_locs.
  Proof.
    rewrite /combine_na_locs. move => [?|] [?|] //=; repeat case_match => //.
    by rewrite (comm (B:=Qp)).
  Qed.
  Global Instance combine_na_locs_assoc : Assoc (=) combine_na_locs.
  Proof.
    rewrite /combine_na_locs. move => [?|] [?|] [?|] //=; repeat case_match => //=; simplify_eq => //.
    by rewrite assoc.
  Qed.

  Lemma combine_na_locs_list_None cols l:
    (∀ π col, cols !! π = Some col → col !! l = None) →
    combine_na_locs_list cols l = Some None.
  Proof.
    elim: cols => //= col cols IH Hπ.
    rewrite (Hπ 0 col) //. rewrite IH // => π col'.
    apply: (Hπ (S _)).
  Qed.

  Lemma combine_na_locs_list_not_excl cols l:
    (∀ π col, cols !! π = Some col → is_not_naexcl (col !! l)) →
    ∃ q, combine_na_locs_list cols l = Some (NaRead <$> q).
  Proof.
    elim: cols => //=. { by eexists None. }
    move => col cols IH Hπ.
    have [|q ->]:= IH.
    { move => ??. by apply: (Hπ (S _)). }
    destruct (col !! l) as [[?[|]]|] eqn: Heq => /=.
    - have := Hπ 0 col. rewrite Heq. naive_solver.
    - destruct q => /=; by eexists (Some _).
    - destruct q => /=; by [eexists (Some _) | eexists None].
  Qed.

  Lemma combine_na_locs_list_single cols col l π:
    cols !! π = Some col →
    (∀ π' col', π' ≠ π → cols !! π' = Some col' → col' !! l = None) →
    combine_na_locs_list cols l = Some (snd <$> (col !! l)).
  Proof.
    elim: cols π => // col' cols IH [|π]/=.
    - move => [->] Hπ. rewrite combine_na_locs_list_None.
      { rewrite /combine_na_locs. repeat case_match => //. }
      move => π col''. by apply: (Hπ (S _)).
    - move => Hcol Hπ. rewrite (Hπ 0) // (IH π) //.
      move => π' col'' ?. apply: (Hπ (S _)). lia.
  Qed.

  Lemma combine_na_locs_list_single_not_excl cols col l π:
    cols !! π = Some col →
    (∀ π' col', π' ≠ π → cols !! π' = Some col' → is_not_naexcl (col' !! l)) →
    ∃ q, combine_na_locs_list cols l = combine_na_locs (Some (snd <$> (col !! l))) (Some (NaRead <$> q)).
  Proof.
    elim: π cols.
    - move => [//|? cols] /= [->] Hπ.
      have [|q ->]:= (combine_na_locs_list_not_excl cols l).
      { move => π ??. by apply: (Hπ (S π)). }
      naive_solver.
    - move => π IH [//| col' cols] /= ? Hπ.
      have [//| | q -> ]:= (IH cols).
      { move => ???. apply: (Hπ (S _)). lia. }
      rewrite (assoc combine_na_locs) (comm _ (Some (snd <$> (col' !! l)))) -(assoc combine_na_locs).
      destruct (col' !! l) as [[?[|]]|] eqn: Heq => /=.
      + have := Hπ 0 col' => /=. rewrite Heq. naive_solver.
      + by destruct q; eexists (Some _).
      + by eexists _.
  Qed.

  Lemma combine_na_locs_list_partial_alter cols l π f col:
    cols !! π = Some col →
    combine_na_locs (Some (snd <$> f (col !! l))) (combine_na_locs_list cols l) =
    combine_na_locs (Some (snd <$> (col !! l))) (combine_na_locs_list (<[π:=(partial_alter f l col)]>cols) l).
  Proof.
    elim: π cols.
    - move => [//|??] /= [->]. rewrite lookup_partial_alter_eq.
      by rewrite assoc (comm _ (Some (snd <$> f (col !! l)))) assoc.
    - move => n IH [//|col' cols] /= ?.
      rewrite assoc (comm _ (Some (snd <$> f (col !! l)))) -assoc IH //.
      by rewrite assoc (comm _ (Some (snd <$> (col' !! l)))) -assoc.
  Qed.

  Lemma combine_na_locs_list_insert cols l π p w col:
    col !! l = None →
    cols !! π = Some col →
    combine_na_locs_list (<[π:=(<[l := (p, w)]> col)]>cols) l = combine_na_locs (Some (Some w)) (combine_na_locs_list cols l).
  Proof.
    move => Hl Hc. have := (combine_na_locs_list_partial_alter _ l _ _ _ Hc).
    by rewrite Hl => /= <-.
  Qed.

  Lemma combine_na_locs_list_delete cols l π p w col:
    col !! l = Some (p, w) →
    cols !! π = Some col →
    combine_na_locs_list cols l = combine_na_locs (Some (Some w)) (combine_na_locs_list (<[π:=(delete l col)]>cols) l).
  Proof.
    move => Hl Hc. have := (combine_na_locs_list_partial_alter _ l _ _ _ Hc).
    by rewrite Hl => /= <-.
  Qed.

  Lemma combine_na_locs_list_partial_alter_ne cols l l' π f col:
    l ≠ l' →
    cols !! π = Some col →
    combine_na_locs_list (<[π:=(partial_alter f l' col)]>cols) l = combine_na_locs_list cols l.
  Proof.
    move => ?.
    elim: π cols.
    - move => [//|??] /= [->]. by rewrite lookup_partial_alter_ne.
    - move => ? IH [//|??] /= ?. by rewrite IH.
  Qed.

  Lemma combine_na_locs_list_snoc_empty cols l:
    combine_na_locs_list (cols ++ [∅]) l = combine_na_locs_list cols l.
  Proof. elim: cols => //= ?? ->. done. Qed.
End combine_na_locs.

Definition alloc_rel_pred (cols : list (gmap loc (loc * na_locs_state))) (l_s : loc) (q : option Qp) : Prop :=
  match combine_na_locs_list cols l_s with
  | None => False
  | Some (Some NaExcl) => q = None
  | Some (Some (NaRead q1)) => if q is Some q2 then q1 + q2 = 1 else False
  | Some None => q = Some 1
  end%Qp.

Definition heap_agree (σ1 σ2 : gmap loc (lock_state * val)) (ls : gset loc) : Prop :=
  ∀ l v v', l ∉ ls → σ1 !! l = Some v → σ2 !! l = Some v' → v = v'.

Definition na_alt_exec (P : prog) (σ : state) (T : list expr) (p : loc) (π : thread_id) (ns : na_locs_state) (excls : gset loc) : Prop :=
  ∃ e σ' K,
    pool_safe P (<[π := fill K e]> T) σ' /\
    (∀ σ, safe_reach P e σ (post_in_ectx (λ e' _, ∃ v' : val, e' = (if ns is NaExcl then Store Na1Ord #p v' else Load Na1Ord #p)))) ∧
    heap_agree σ.(heap) σ'.(heap) excls ∧
    heap_wf σ' ∧
    σ'.(used_dyn_blocks) ⊆ σ.(used_dyn_blocks) ∧
    σ'.(globals) = σ.(globals).

Definition na_locs_wf (cols : list (gmap loc (loc * na_locs_state))) (P_s : prog) (σ_s : state) (T_s : list expr) : Prop :=
  ∀ (π : nat) col, cols !! π = Some col →
   ∃ (lcol : list (loc * na_locs_state)),
     (∀ (p_s : loc) p_t ns, col !! p_s = Some (p_t, ns) → (p_s, ns) ∈ lcol) ∧
     ∀ (p_s : loc) ns, (p_s, ns) ∈ lcol →
      na_alt_exec P_s σ_s T_s p_s π ns (list_to_set (fst <$> filter (λ x, x.2 = NaExcl) lcol)).

Section na_alt_exec.

  Lemma na_alt_exec_intro ns σ_s' P_s σ_s T_s π K_s (l_s : loc) ls e:
    heap_wf σ_s' →
    used_dyn_blocks σ_s' ⊆ used_dyn_blocks σ_s →
    globals σ_s' = globals σ_s →
    (∀ l, l ∉ ls → σ_s.(heap) !! l = σ_s'.(heap) !! l) →
    pool_safe P_s (<[π:=fill K_s e]> T_s) σ_s' →
    (∀ σ, safe_reach P_s e σ (post_in_ectx (λ e' _, ∃ v' : val, e' = (if ns is NaExcl then Store Na1Ord #l_s v' else Load Na1Ord #l_s)))) →
    na_alt_exec P_s σ_s T_s l_s π ns ls.
  Proof.
    move => ??? Hh ??. eexists _, _, _.
    split_and!; [done | done | move => ????; rewrite Hh => *; by simplify_eq | done | done | done].
  Qed.

  Lemma na_alt_exec_mono P_s σ_s σ_s' T_s T_s' π (l_s : loc) ns ls ls':
    na_alt_exec P_s σ_s' T_s' l_s π ns ls' →
    (∀ σ', heap_wf σ' → used_dyn_blocks σ' ⊆ used_dyn_blocks σ_s' →
           heap_agree σ_s'.(heap) σ'.(heap) ls' → heap_agree σ_s.(heap) σ'.(heap) ls) →
    used_dyn_blocks σ_s' ⊆ used_dyn_blocks σ_s →
    globals σ_s' = globals σ_s →
    (∀ e, <[π:=e]>T_s = <[π:=e]>T_s' ) →
    (ls' ⊆ ls) →
    na_alt_exec P_s σ_s T_s l_s π ns ls.
  Proof.
    move => [e[σ_s''[K_s' [Hsafe [? [Hl [?[??]]]]]]]] Hσ ?? HT Hls.
    eexists _, _, _. split_and!.
    - by rewrite HT.
    - naive_solver.
    - naive_solver.
    - done.
    - set_solver.
    - congruence.
  Qed.

  Lemma na_alt_exec_load_stuck o P_s σ_s T_s π π' K_s e_s (l_s : loc) ls:
    na_alt_exec P_s σ_s T_s l_s π' NaExcl ls →
    T_s !! π = Some (fill K_s e_s) →
    π' < length T_s →
    o ≠ Na2Ord →
    π ≠ π' →
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' _, e' = Load o #l_s))) →
    False.
  Proof.
    move => [e [σ' [K [Hsafe [He Hσ]]]]] HT ? ? ? Hsteps.
    eapply pool_reach_stuck_not_safe; last apply Hsafe.
    apply: pool_safe_safe_reach_stuck; first done.
    { by apply list_lookup_insert_eq. }
    { by apply: fill_safe_reach. }
    move => ?? [?[?[-> [? ->]]]]. rewrite list_insert_insert_eq => Hsafe'.
    apply: pool_safe_safe_reach_stuck; first done.
    { by rewrite list_lookup_insert_ne. }
    { apply: fill_safe_reach. by apply: Hsteps. }
    move => ?? [? [? [-> ->]]]. intros Hsafe''.
    eapply pool_safe_implies_app; [ | | apply Hsafe'' | ].
    2: { rewrite list_lookup_insert_ne //. by apply: list_lookup_insert_eq. }
    { apply _. }
    move => [?[?[??]]]; simplify_eq.
    apply: (pool_reach_stuck_no_forks π').
    { rewrite list_lookup_insert_ne //. by apply list_lookup_insert_eq. }
    { apply: fill_no_forks. apply: no_forks_step; [|by apply: no_forks_refl].
        apply: base_prim_step. by constructor. }
    apply: pool_reach_stuck_reach_stuck.
    2: { rewrite list_lookup_insert_ne //. apply list_lookup_insert_eq.
         rewrite length_insert. by apply: lookup_lt_Some. }
    apply: stuck_reach_stuck. apply: fill_stuck.
    apply: base_stuck_stuck; [|solve_sub_redexes_are_values].
    split; [done|] => ??? Hstep. inversion Hstep; simplify_map_eq/=.
  Qed.

  Lemma na_alt_exec_store_stuck o P_s σ_s T_s π π' K_s e_s (l_s : loc) ls ns:
    na_alt_exec P_s σ_s T_s l_s π' ns ls →
    T_s !! π = Some (fill K_s e_s) →
    π' < length T_s →
    o ≠ Na2Ord →
    π ≠ π' →
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' _, ∃ v' : val, e' = Store o #l_s v'))) →
    False.
  Proof.
    move => [e [σ' [K [Hsafe [He Hσ]]]]] HT ? ? ? Hsteps.
    eapply pool_reach_stuck_not_safe; last apply Hsafe.
    apply: (pool_safe_safe_reach_stuck); first done.
    { by apply list_lookup_insert_eq. }
    { by apply: fill_safe_reach. }
    move => ?? [?[?[-> [? ->]]]]. rewrite list_insert_insert_eq => Hsafe'.
    apply: pool_safe_safe_reach_stuck; first done.
    { by rewrite list_lookup_insert_ne. }
    { apply: fill_safe_reach. by apply: Hsteps. }
    move => ?? [? [? [-> [? ->]]]] Hsafe''.
    destruct ns.
    - eapply (pool_safe_implies_app); [ | | apply Hsafe'' | ].
      2: { rewrite list_lookup_insert_ne //. by apply: list_lookup_insert_eq. }
      { apply _. }
      move => [?[?[??]]]; simplify_eq.
      apply: (pool_reach_stuck_no_forks π').
      { rewrite list_lookup_insert_ne //. by apply list_lookup_insert_eq. }
      { apply: fill_no_forks. apply: no_forks_step; [|by apply: no_forks_refl].
        apply: base_prim_step. by constructor. }
      apply: pool_reach_stuck_reach_stuck.
      2: { rewrite list_lookup_insert_ne //. apply list_lookup_insert_eq.
           rewrite length_insert. by apply: lookup_lt_Some. }
      apply: stuck_reach_stuck. apply: fill_stuck.
      apply: base_stuck_stuck; [|solve_sub_redexes_are_values].
      split; [done|] => ??? Hstep. inversion Hstep; simplify_map_eq/=.
    - eapply (pool_safe_implies_app); [ | | apply Hsafe'' | ].
      2: { rewrite list_lookup_insert_ne //. by apply: list_lookup_insert_eq. }
      { apply _. }
      move => [?[?[?[??]]]]; simplify_eq.
      apply: (pool_reach_stuck_no_forks π').
      { rewrite list_lookup_insert_ne //. by apply list_lookup_insert_eq. }
      { apply: fill_no_forks. apply: no_forks_step; [|by apply: no_forks_refl].
        apply: base_prim_step. by constructor. }
      apply: pool_reach_stuck_reach_stuck.
      2: { rewrite list_lookup_insert_ne //. apply list_lookup_insert_eq.
           rewrite length_insert. by apply: lookup_lt_Some. }
      apply: stuck_reach_stuck. apply: fill_stuck.
      apply: base_stuck_stuck; [|solve_sub_redexes_are_values].
      split; [done|] => ??? Hstep. inversion Hstep; simplify_map_eq/=.
  Qed.

  Lemma na_alt_exec_free_stuck P_s σ_s T_s π π' K_s e_s (n : Z) (l_s : loc) ls ns i:
    na_alt_exec P_s σ_s T_s (l_s +ₗ i) π' ns ls →
    T_s !! π = Some (fill K_s e_s) →
    π' < length T_s →
    π ≠ π' →
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' _, e' = FreeN #n #l_s))) →
    False.
  Proof.
    move => [e [σ' [K [Hsafe [He Hσ]]]]] HT ? ? Hsteps .
    eapply pool_reach_stuck_not_safe; last apply Hsafe.
    apply: (pool_safe_safe_reach_stuck); first done.
    { by apply list_lookup_insert_eq. }
    { by apply: fill_safe_reach. }
    move => ?? [?[?[-> [? ->]]]]. rewrite list_insert_insert_eq => Hsafe'.
    apply: pool_safe_safe_reach_stuck; first done.
    { by rewrite list_lookup_insert_ne. }
    { apply: fill_safe_reach. by apply: Hsteps. }
    move => ?? [? [? [-> ->]]] => Hsafe''.
    eapply (pool_safe_implies_app); [ | | apply Hsafe'' | ].
    2: { apply: list_lookup_insert_eq. rewrite length_insert. by apply: lookup_lt_Some. }
    { apply _. }
    move => [?[?[?[?[? [? Hs]]]]]]; simplify_eq.
    apply: pool_reach_stuck_no_forks.
    { apply: list_lookup_insert_eq. rewrite length_insert. by apply: lookup_lt_Some. }
    { apply: no_forks_step; [|apply no_forks_refl]. apply: fill_no_fork.
      apply: base_prim_step. by econstructor. }
    rewrite list_insert_insert_eq list_insert_insert_ne //.
    apply: pool_reach_stuck_reach_stuck.
    2: { apply: list_lookup_insert_eq. by rewrite length_insert. }
    apply: fill_reach_stuck.
    eapply pool_safe_no_forks in Hsafe''.
    2: { apply: list_lookup_insert_eq. rewrite length_insert. by apply: lookup_lt_Some. }
    2: { apply: no_forks_step; [|apply no_forks_refl]. apply: fill_no_fork.
      apply: base_prim_step. by econstructor. }
    rewrite list_insert_insert_eq list_insert_insert_ne // in Hsafe''.
    destruct ns; (eapply (pool_safe_implies_app _ _ π'); [ | | apply Hsafe'' | ];
      [ | apply list_lookup_insert_eq; by rewrite length_insert | ]; first apply _).
    - move => [?[?[? Hh]]]; simplify_eq/=.
      move: Hh => /lookup_free_mem_Some /= [/(mk_is_Some _ _) /Hs ?[//|?]]. lia.
    - move => [?[?[? [? Hh]]]]; simplify_eq/=.
      move: Hh => /lookup_free_mem_Some /= [/(mk_is_Some _ _) /Hs ?[//|?]]. lia.
  Qed.

  Lemma na_alt_exec_step P_s σ_s σ_s' T_s π π' ns ls e e' l_s K_s:
    na_alt_exec P_s σ_s T_s l_s π' ns ls →
    T_s !! π = Some (fill K_s e) →
    π ≠ π' →
    (∀ σ, heap_wf σ →
        used_dyn_blocks σ ⊆ used_dyn_blocks σ_s →
        globals σ = globals σ_s →
        (∀ l v1 v2, l∉ls → σ_s.(heap) !! l = Some v1 → σ.(heap) !! l = Some v2 → v1 = v2) →
        safe_reach P_s e σ (λ e σ',
        e = e' ∧
        (∀ l v1 v2, l∉ls → σ_s'.(heap) !! l = Some v1 → σ'.(heap) !! l = Some v2 → v1 = v2) ∧
        heap_wf σ' ∧
        used_dyn_blocks σ' ⊆ used_dyn_blocks σ_s' ∧
        globals σ' = globals σ_s'
    )) →
    na_alt_exec P_s σ_s' (<[π := fill K_s e']>T_s) l_s π' ns ls.
  Proof.
    move => [e'' [σ_s''[K_s' [Hsafe [He [Hl [?[??]]]]]]]] HT Hπ Hsteps.
    have [|?[?[[? [Hh [?[??]]]]?]]]:= (pool_safe_safe_reach π _ _ _ _ _ K_s ltac:(done) _ ltac:(clear He; naive_solver)); simplify_eq.
    { by rewrite list_lookup_insert_ne. }
    eexists _, _, _. split_and!.
    - by rewrite list_insert_insert_ne.
    - done.
    - done.
    - done.
    - done.
    - done.
  Qed.

  Lemma na_alt_exec_fork P σ π π' T e e' p ns ls efs:
    na_alt_exec P σ T p π' ns ls →
    T !! π = Some e →
    π ≠ π' →
    π' < length T →
    (∀ σ, prim_step P e σ e' σ efs) →
    na_alt_exec P σ (<[π:=e']> T ++ efs) p π' ns ls.
  Proof.
    move => [e''[σ' [K [? ?]]]] HT ? ? Hstep.
    move: (HT) => /(lookup_lt_Some _ _ _)?.
    rewrite -insert_app_l //.
    eexists _, _, _. split; [|done].
    rewrite list_insert_insert_ne //.
    apply: pool_steps_safe; [|done].
    apply/pool_steps_single.
    rewrite !insert_app_l // ?length_insert //.
    apply: prim_step_pool_step; [ by apply Hstep |].
    by rewrite list_lookup_insert_ne.
  Qed.

  Lemma na_alt_exec_pure P σ π π' T e e' p ns ls:
    na_alt_exec P σ T p π' ns ls →
    T !! π = Some e →
    (∀ σ', σ'.(globals) = σ.(globals) → prim_step P e σ' e' σ' []) →
    na_alt_exec P σ (<[π:=e']> T) p π' ns ls.
  Proof.
    move => [e'' [σ' [K [? [?[?[?[??]]]]]]]] HT Hstep.
    eexists _, _, _. split; [|done].
    destruct (decide (π' = π)); subst.
    - by rewrite list_insert_insert_eq.
    - rewrite list_insert_insert_ne //.
      apply: pool_steps_safe; [|done].
      apply/pool_steps_single/no_fork_pool_step; [ by apply Hstep |].
      by rewrite list_lookup_insert_ne.
  Qed.
End na_alt_exec.

Section na_locs_wf.
  Lemma na_locs_wf_init P σ e:
    na_locs_wf [∅] P σ [e].
  Proof. move => ???. simplify_list_eq. eexists []. set_solver. Qed.

  Lemma na_locs_wf_combined_state_load cols P_s σ_s T_s π K_s e_s o (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s e_s) →
    o ≠ Na2Ord →
    length cols = length T_s →
    cols !! π = Some col →
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' _, e' = Load o #l_s))) →
    ∃ q : option Qp, combine_na_locs_list cols l_s = combine_na_locs (Some (snd <$> (col !! l_s))) (Some (NaRead <$> q)).
  Proof.
    move => Hwf HT ? Hlen Hcols Hsteps.
    apply: combine_na_locs_list_single_not_excl; [done|].
    move => π' col' Hneq Hπ'. move: (Hπ') => /(lookup_lt_Some _ _ _)Hlt.
    rewrite Hlen in Hlt.
    destruct (col' !! l_s) as [[?[]]|] eqn:Hl_s; [exfalso|done..].
    have [lcol [Hlcol {}Hwf]]:= Hwf π' _ Hπ'.
    have {}Hl_s:= Hlcol _ _ _ Hl_s.
    apply: na_alt_exec_load_stuck; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_combined_state_store cols P_s σ_s T_s π K_s e_s o (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s e_s) →
    o ≠ Na2Ord →
    length cols = length T_s →
    cols !! π = Some col →
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' _, ∃ v' : val, e' = Store o #l_s v'))) →
    combine_na_locs_list cols l_s = Some (snd <$> (col !! l_s)).
  Proof.
    move => Hwf HT ? Hlen Hcols Hsteps.
    apply: combine_na_locs_list_single; [done|].
    move => π' col' Hneq Hπ'. move: (Hπ') => /(lookup_lt_Some _ _ _)Hlt.
    rewrite Hlen in Hlt.
    destruct (col' !! l_s) as [[??]|] eqn:Hl_s; [exfalso|done].
    have [lcol [Hlcol {}Hwf]]:= Hwf π' _ Hπ'.
    have {}Hl_s:= Hlcol _ _ _ Hl_s.
    apply: na_alt_exec_store_stuck; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_combined_state_Free cols P_s σ_s T_s π K_s e_s (n : Z) (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s e_s) →
    length cols = length T_s →
    cols !! π = Some col →
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' _, e' = FreeN #n #l_s))) →
    ∀ i, combine_na_locs_list cols (l_s +ₗ i) = Some (snd <$> (col !! (l_s +ₗ i))).
  Proof.
    move => Hwf HT Hlen Hcols Hsteps i.
    apply: combine_na_locs_list_single; [done|].
    move => π' col' Hneq Hπ'. move: (Hπ') => /(lookup_lt_Some _ _ _)Hlt.
    rewrite Hlen in Hlt.
    destruct (col' !! (l_s +ₗ i)) as [[??]|] eqn:Hl_s; [exfalso|done].
    have [lcol [Hlcol {}Hwf]]:= Hwf π' _ Hπ'.
    have {}Hl_s:= Hlcol _ _ _ Hl_s.
    apply: na_alt_exec_free_stuck; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_insert_store cols P_s σ_s T_s π K_s (l_s : loc) l_t col e:
    na_locs_wf cols P_s σ_s T_s →
    heap_wf σ_s →
    cols !! π = Some col →
    pool_safe P_s (<[π:=fill K_s e]> T_s) σ_s →
    (∀ σ, safe_reach P_s e σ (post_in_ectx (λ e' _, ∃ v' : val, e' = (#l_s <- v')%E ))) →
    na_locs_wf (<[π:=<[l_s := (l_t, NaExcl)]>col]>cols) P_s σ_s T_s.
  Proof.
    move => Hwf ? Hcols Hsafe He π' col' Hlookup.
    destruct (decide (π' = π)); simplify_eq.
    - rewrite list_lookup_insert_eq in Hlookup; [|by apply: lookup_lt_Some]; simplify_eq.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcols.
      eexists ((l_s, NaExcl)::lcol).
      split.
      + move => ??? /lookup_insert_Some. set_solver.
      + move => p_s ws. rewrite filter_cons_True //; csimpl.
        move => /elem_of_cons[?|Hp]; simplify_eq.
        * by apply: na_alt_exec_intro.
        * apply: na_alt_exec_mono; [naive_solver| |done|done|done|set_solver].
          move => ? ?? Ha ????. apply: Ha. set_solver.
    - rewrite list_lookup_insert_ne // in Hlookup.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hlookup.
      eexists lcol. naive_solver.
  Qed.

  Lemma na_locs_wf_insert_load cols P_s σ_s T_s π K_s (l_s : loc) l_t col q e:
    na_locs_wf cols P_s σ_s T_s →
    heap_wf σ_s →
    cols !! π = Some col →
    pool_safe P_s (<[π:=fill K_s e]> T_s) σ_s →
    (∀ σ, safe_reach P_s e σ (post_in_ectx (λ e' _, e' = (! #l_s)%E ))) →
    na_locs_wf (<[π:=<[l_s := (l_t, NaRead q)]>col]>cols) P_s σ_s T_s.
  Proof.
    move => Hwf ? Hcols Hnfs He π' col' Hlookup.
    destruct (decide (π' = π)); simplify_eq.
    - rewrite list_lookup_insert_eq in Hlookup; [|by apply: lookup_lt_Some]; simplify_eq.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcols.
      eexists ((l_s, NaRead q)::lcol).
      split.
      + move => ??? /lookup_insert_Some. set_solver.
      + move => p_s ws. rewrite filter_cons_False //=.
        move => /elem_of_cons[?|Hp]; simplify_eq.
        * apply: (na_alt_exec_intro); [done..|] => ?. apply: safe_reach_mono; [done|].
          move => ???. apply: post_in_ectx_mono; [done|]. eexists #(). naive_solver.
        * naive_solver.
    - rewrite list_lookup_insert_ne // in Hlookup.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hlookup.
      eexists lcol. naive_solver.
  Qed.

  Lemma na_locs_wf_delete cols P_s σ_s T_s π (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    cols !! π = Some col →
    na_locs_wf (<[π:=delete l_s col]>cols) P_s σ_s T_s.
  Proof.
    move => Hwf Hcol π' col' Hcol'.
    move: (Hcol) => /(lookup_lt_Some _ _ _)?.
    destruct (decide (π = π')); subst.
    2: { apply: Hwf. by rewrite list_lookup_insert_ne in Hcol'. }
    rewrite list_lookup_insert_eq // in Hcol'; simplify_eq.
    have [lcol [? {}Hwf]]:= Hwf _ _ Hcol.
    eexists lcol. split; [|done].
    move => ??? /lookup_delete_Some[??]. naive_solver.
  Qed.

  Lemma na_locs_wf_pure cols P_s σ_s T π e_s e_s':
    na_locs_wf cols P_s σ_s T →
    T !! π = Some e_s →
    (∀ σ_s', σ_s'.(globals) = σ_s.(globals) → prim_step P_s e_s σ_s' e_s' σ_s' []) →
    na_locs_wf cols P_s σ_s (<[π:=e_s']> T).
  Proof.
    move => Hwf HT Hstep π' col Hcol.
    have [lcol [Hlcol {}Hwf]]:= Hwf π' col Hcol.
    eexists lcol. split; [done|]. move => p_s ws Hp.
    apply: na_alt_exec_pure; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_store σ_s (l_s : loc) (v v' : val) T_s π K_s P_s cols col o:
    na_locs_wf cols P_s σ_s T_s →
    cols !! π = Some col →
    o = Na1Ord ∨ (o = ScOrd ∧
     (∀ (l_s' : loc) l_t' ns σ_s,
        col !! l_s' = Some (l_t', ns) →
        safe_reach P_s (fill K_s #()) σ_s (post_in_ectx (λ e' σ', ∃ v' : val, e' = (if ns is NaExcl then Store Na1Ord #l_s' v' else Load Na1Ord #l_s'))))) →
    heap σ_s !! l_s = Some (RSt 0, v) →
    T_s !! π = Some (fill K_s (Store o #l_s v')) →
    pool_safe P_s T_s σ_s →
    heap_wf σ_s →
    length cols = length T_s →
    na_locs_wf cols P_s (state_upd_heap <[l_s:=(RSt 0, v')]> σ_s) (<[π:=fill K_s #()]> T_s).
  Proof.
    move => Hwf Hcols Hexcl ? ? ? ? Hlen π' col' Hcol'.
    have ? : o ≠ Na2Ord by naive_solver.
    move: (Hcol') => /(lookup_lt_Some _ _ _)Hlt. rewrite Hlen in Hlt.
    destruct (decide (π = π')); simplify_eq.
    - have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcols.
      destruct Hexcl as [?|[? Hcol]]; simplify_map_eq.
      + eexists ((l_s, NaExcl)::lcol).
        split; [set_solver|].
        move => p_s ws. rewrite filter_cons_True //; csimpl.
        move => /elem_of_cons[?|Hp]; simplify_eq.
        * apply: na_alt_exec_intro; [done|done|done | | |].
          -- move => l ?. have ? : l ≠ l_s by set_solver.
               by rewrite lookup_insert_ne.
          -- by rewrite list_insert_insert_eq list_insert_id.
          -- move => ?. apply safe_reach_refl. apply: post_in_ectx_intro. naive_solver.
        * apply: na_alt_exec_mono; [naive_solver| |done| done| |set_solver].
          -- move => σ' ?? Ha l ???. have ? : l ≠ l_s by set_solver.
             rewrite lookup_insert_ne //. apply: Ha. set_solver.
          -- move => ?. by rewrite list_insert_insert_eq.
      + eexists (map_to_list (snd <$> col)). split.
        { move => ????. apply elem_of_map_to_list. by simplify_map_eq. }
        move => ?? /elem_of_map_to_list/lookup_fmap_Some[[??][??]]; simplify_eq/=.
        apply: na_alt_exec_intro.
        * eapply heap_wf_insert; [done|]. naive_solver.
        * done.
        * done.
        * done.
        * erewrite fill_empty. rewrite list_insert_insert_eq. apply: pool_safe_no_forks; [done|done|].
          apply: fill_no_forks. apply: no_forks_step. { apply: base_prim_step. by econstructor. }
          apply: no_forks_refl.
        * naive_solver.
    - have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
      eexists lcol. split; [done|] => p_s ws Hp.
      destruct (decide (l_s = p_s)); subst.
      + exfalso. apply: (na_alt_exec_store_stuck o); [naive_solver | done | done | naive_solver |done | ].
        move => ??. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver.
      + apply: na_alt_exec_step; [naive_solver |done |done |].
        move => ?????.
        apply: safe_reach_safe_implies. move => [?[?[[<-]?]]]; simplify_eq.
        apply: safe_reach_store; [done|].
        apply: safe_reach_refl. split_and!; [done| | by apply: heap_wf_insert; eauto |done|done].
        move => l' ?? /= ???. destruct (decide (l' = l_s)); simplify_map_eq => //. naive_solver.
  Qed.

  Lemma na_locs_wf_load σ_s (l_s : loc) n (v : val) T_s π K_s P_s cols o:
    na_locs_wf cols P_s σ_s T_s →
    heap σ_s !! l_s = Some (RSt n, v) →
    T_s !! π = Some (fill K_s (Load o #l_s)) →
    o ≠ Na2Ord →
    pool_safe P_s T_s σ_s →
    length cols = length T_s →
    na_locs_wf cols P_s σ_s (<[π:=fill K_s v]> T_s).
  Proof.
    move => Hwf ? ? ? ? Hlen π' col' Hcol'.
    move: (Hcol') => /(lookup_lt_Some _ _ _)Hlt. rewrite Hlen in Hlt.
    destruct (decide (π = π')); subst.
    { unfold na_alt_exec. setoid_rewrite list_insert_insert_eq. by apply: Hwf. }
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    eexists lcol. split; [done|] => p_s ws Hp.
    destruct (decide ((l_s, NaExcl) ∈ lcol)) as [Hin|Hin].
    - exfalso. apply: (na_alt_exec_load_stuck o); [naive_solver | done |done|done | done |].
      move => ??. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver.
    - apply: na_alt_exec_step; [naive_solver |done |done |].
      move => ???? Heq.
      apply: safe_reach_safe_implies. move => [?[?[?[??]]]]; simplify_eq.
      apply: safe_reach_load; [done..|].
      apply: safe_reach_refl. split_and!; [|done|done|done|done].
      opose proof* Heq; [|done|done|naive_solver].
      rewrite not_elem_of_list_to_set list_elem_of_fmap.
      move => [[??][?]]. rewrite list_elem_of_filter. naive_solver.
  Qed.

  Lemma na_locs_wf_alloc cols P_s σ_s n T_s π (v : val) K_s:
    na_locs_wf cols P_s σ_s T_s →
    (0 < n)%Z →
    T_s !! π = Some (fill K_s (AllocN #n v)) →
    heap_wf σ_s →
    na_locs_wf cols P_s
         {| heap :=
             heap_array (dyn_loc (fresh (used_dyn_blocks σ_s)))
               (replicate (Z.to_nat n) v) ∪ heap σ_s;
           used_dyn_blocks := {[fresh (used_dyn_blocks σ_s)]} ∪ used_dyn_blocks σ_s;
           globals := globals σ_s
         |} (<[π:=fill K_s #(dyn_loc (fresh (used_dyn_blocks σ_s)))]> T_s).
  Proof.
    move => Hwf ? HT Hσwf π' col' Hcol'.
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    eexists lcol. split; [done|] => p_s ws Hp.
    destruct (decide (π = π')); simplify_eq.
    - apply: na_alt_exec_mono; [naive_solver | | set_solver |done | |done].
      2: { move => ?. by rewrite list_insert_insert_eq. }
      move => ? Hhwf Hsub Ha ???? /lookup_union_Some [|/heap_array_lookup [?[?[?[?[??]]]]]|]; simplify_eq.
      { apply heap_array_map_disjoint => ???. apply eq_None_not_Some => -[? /Hσwf]. apply is_fresh. }
      + move => /Hhwf /Hsub /(is_fresh _)[].
      + by apply: Ha.
    - apply: na_alt_exec_step; [naive_solver |done |done |].
      move => σ' Hhwf Hsub Hg Heq.
      apply: safe_reach_base_step.
      2: apply: safe_reach_refl; split; [done|].
      { econstructor; [done| |].
        - move => /Hsub /(is_fresh _)[].
        - move => i. apply eq_None_not_Some => -[? /Hhwf] /Hsub. apply is_fresh.
      }
      split_and!.
      + move => ???? /lookup_union_Some_raw[/heap_array_lookup[?[?[?[?[??]]]]]|[??]]
                    /lookup_union_Some_raw[/heap_array_lookup[?[?[?[?[??]]]]]|[??]]; simplify_eq => //.
        * exfalso. apply: eq_None_ne_Some_1; [done|]. apply heap_array_lookup. naive_solver.
        * exfalso. apply: eq_None_ne_Some_1; [done|]. apply heap_array_lookup. naive_solver.
        * by apply: Heq.
      + by apply: heap_wf_init_mem.
      + set_solver.
      + done.
  Qed.

  Lemma na_locs_wf_free cols P_s σ_s T_s π (n : Z) (l : loc) K_s:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s (FreeN #n #l)) →
    na_locs_wf cols P_s (state_upd_heap (free_mem l (Z.to_nat n)) σ_s) (<[π:=fill K_s #()]> T_s).
  Proof.
    move => Hwf HT π' col' Hcol'.
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    eexists lcol. split; [done|] => p_s ws Hp.
    destruct (decide (π = π')); simplify_eq.
    - apply: na_alt_exec_mono; [naive_solver | | set_solver | done| |done].
      2: { move => ?. by rewrite list_insert_insert_eq. }
      move => /= ??? Hl???? /lookup_free_mem_Some[??]. by apply: Hl.
    - apply: na_alt_exec_step; [naive_solver |done |done |].
      move => σ' Hhwf Hsub Hg Heq.
      eapply safe_reach_safe_implies; [apply _|].
      move => [?[?[?[?[?[??]]]]]]; simplify_eq.
      apply: safe_reach_base_step; [by econstructor|].
      apply: safe_reach_refl; split_and!; [done| | by apply: heap_wf_free_mem |done |done].
      move => ???? /lookup_free_mem_Some[??] /lookup_free_mem_Some[??]. by apply: Heq.
  Qed.

  Lemma na_locs_wf_fork cols P_s σ_s T_s K_s e_s π:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s (Fork e_s)) →
    cols !! π = Some ∅ →
    length T_s = length cols →
    na_locs_wf (cols ++ [∅]) P_s σ_s (<[π:=fill K_s #()]> T_s ++ [e_s]).
  Proof.
    move => Hwf HT ? Hlen π' col' /lookup_app_Some[Hcol'|[?/(list_elem_of_split_length _ _ _) [[|?[|??]][?[??]]]]]; simplify_eq.
    2: { eexists []. split; [by simplify_list_eq|set_solver]. }
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    destruct (decide (π = π')); simplify_map_eq.
    { eexists []. split; [by simplify_list_eq|set_solver]. }
    eexists lcol. split; [done|] => p_s ws Hp; simplify_eq/=.
    apply: na_alt_exec_fork; [naive_solver|done.. | |].
    { rewrite Hlen. by apply: lookup_lt_Some. }
    move => ?. apply: fill_prim_step. apply: base_prim_step. econstructor.
  Qed.
End na_locs_wf.


Definition na_locs_in_L (cols : list (gmap loc (loc * na_locs_state))) (L : gset (block * block)) : Prop :=
  ∀ π col l x, cols !! π = Some col → col !! l = Some x → ∃ b1, (b1, loc_block l) ∈ L.

Section na_locs_in_L.
  Lemma na_locs_in_L_init L:
    na_locs_in_L [∅] L.
  Proof. move => ??????. simplify_list_eq. Qed.

  Lemma na_locs_in_L_extend cols L b_t b_s:
    na_locs_in_L cols L →
    na_locs_in_L cols ({[(b_t, b_s)]} ∪ L).
  Proof. move => Hwf π col l x Hcol Hx. have [??]:= Hwf π col l x Hcol Hx. set_solver. Qed.
End na_locs_in_L.
