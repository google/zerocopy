From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional .
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Import slsls lifting gen_log_rel.
From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.simulang Require Export class_instances primitive_laws heapbij gen_val_rel globalbij.
From simuliris.simulang.na_inv Require Export na_locs.


(** * Instance of the SimpLang program logic that provides a means of establishing bijections on the heap and includes reasoning about data-races. *)

Class naGS (Σ : gFunctors) := NaGS {
  naGS_heapGS :: sheapGS Σ;
  naGS_bijGS :: heapbijGS Σ;
  naGS_col_mapG :: ghost_mapG Σ nat (gmap loc (loc * na_locs_state));
  naGS_col_name : gname;
}.

Section definitions.
  Context `{naGS Σ}.
  Definition na_locs (π : thread_id) (col : gmap loc (loc * na_locs_state)) : iProp Σ :=
    π ↪[ naGS_col_name ] col.

  Definition na_bij_interp (P_s : prog) (σ_s : state) (T_s : list expr) :=
    (∃ L cols,
        ⌜length cols = length T_s⌝ ∗
        ⌜na_locs_wf cols P_s σ_s T_s⌝ ∗
        ⌜na_locs_in_L cols L⌝ ∗
        ghost_map_auth_frac naGS_col_name 1 (map_seq 0 cols) ∗
        heapbij_interp L (λ _, alloc_rel_pred cols) ∗
        globalbij_interp loc_rel)%I.
End definitions.

Section laws.
  Context `{naGS Σ}.
  Implicit Types (b_t b_s : block) (l_t l_s : loc).

  Lemma na_bij_access b_t b_s P_s σ_s T_s:
    na_bij_interp P_s σ_s T_s -∗
    block_rel b_t b_s -∗
    ∃ cols, ⌜length cols = length T_s⌝ ∗ ⌜na_locs_wf cols P_s σ_s T_s⌝ ∗
    ghost_map_auth_frac naGS_col_name 1 (map_seq 0 cols) ∗
    (alloc_rel b_t b_s (λ _, alloc_rel_pred cols)) ∗
    (∀ cols' σ_s' T_s',
        ⌜length cols' = length T_s'⌝ -∗ ⌜na_locs_wf cols' P_s σ_s' T_s'⌝ -∗
        ⌜∀ π col l_s w, cols' !! π = Some col → col !! l_s = Some w → loc_block l_s = b_s ∨ ∃ col' w', cols !! π = Some col' ∧ col' !! l_s = Some  w'⌝ -∗
        ⌜∀ b' o' q, b' ≠ b_s → alloc_rel_pred cols (Loc b' o') q → alloc_rel_pred cols' (Loc b' o') q⌝ -∗
        ghost_map_auth_frac naGS_col_name 1 (map_seq 0 cols') -∗ alloc_rel b_t b_s (λ _, alloc_rel_pred cols') -∗ na_bij_interp P_s σ_s' T_s').
  Proof.
    iIntros "Hinv Hrel". iDestruct "Hinv" as (L cols ? ? HL) "(Hcols & Hbij & Hgs)".
    iExists _. do 2 (iSplit; [done|]). iFrame.
    iDestruct (heapbij_access with "Hbij Hrel") as (?) "[$ Hclose]".
    iIntros (cols' σ_s' T_s' ? ? Hdom HP) "Hcols He". iExists L, cols'. iFrame. repeat (iSplit; [done|]).
    iSplit.
    { iPureIntro => ??????. opose proof* Hdom as Hd; [done.. | ].
      destruct Hd as [->|[?[??]]].
      - naive_solver.
      - apply: HL; naive_solver.
    }
    iApply ("Hclose" with "[%] He").
    move => ????. naive_solver.
  Qed.
End laws.

Notation val_rel := (gen_val_rel heapbij.loc_rel).
Notation log_rel := (gen_log_rel val_rel (λ π, na_locs π ∅)).

Section fix_heap.
  Context `{naGS Σ}.

  Global Program Instance na_inv : sheapInv Σ := {|
    sheap_inv P_s σ_s T_s := na_bij_interp P_s σ_s T_s;
    sheap_ext_rel π v_t v_s := na_locs π ∅ ∗ val_rel v_t v_s;
  |}%I.
  Next Obligation.
    iIntros (????????) "(%L & %cols & % & % & ? &?)".
    iExists _,_. iFrame. iPureIntro.
    rewrite length_insert. split; [done|].
    by apply: na_locs_wf_pure.
  Qed.

  Global Instance na_inv_supports_alloc : sheapInvSupportsAlloc.
  Proof.
    constructor. iIntros (???????????) "(%L&%cols&%Hlen&%Hwf&?&?&?&?)".
    iExists _,_. iFrame. iPureIntro. rewrite length_insert. split; [done|].
    by apply: na_locs_wf_alloc.
  Qed.
  Global Instance na_inv_supports_free : sheapInvSupportsFree.
  Proof.
    constructor. iIntros (???????????) "(%L&%cols&%Hlen&%Hwf&?&?&?&?)".
    iExists _, _. iFrame. iPureIntro. rewrite length_insert. split; [done|].
    by apply: na_locs_wf_free.
  Qed.
  Global Instance na_inv_supports_load o : sheapInvSupportsLoad o.
  Proof.
    constructor. iIntros (?????????????) "(%L&%cols&%Hlen&%Hwf&?&?&?&?)".
    iExists _, _. iFrame. iPureIntro. rewrite length_insert. split; [done|].
    by apply: na_locs_wf_load.
  Qed.
  Global Instance na_inv_supports_store : sheapInvSupportsStore Na1Ord.
  Proof.
    constructor. iIntros (??????? π ????) "(%L&%cols&%Hlen&%Hwf&?&?&?&?)".
    iExists _, _. iFrame. iPureIntro. rewrite length_insert. split; [done|].
    have [|??]:= lookup_lt_is_Some_2 cols π. { rewrite Hlen. by apply: lookup_lt_Some. }
    apply: na_locs_wf_store; [done | done | by left | done | done |done | done |done].
  Qed.

  Lemma sim_bij_contains_globalbij :
    sheap_inv_contains_globalbij loc_rel.
  Proof. by iIntros (???) "(%L&%cols&?&?&?&?&?&$)". Qed.

  Lemma sim_bij_exploit_store π l_t (l_s : loc) Φ e_s e_t col:
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' σ', ∃ v' : val, e' = Store Na1Ord #l_s v' ∧ ∃ v, σ_s.(heap) !! l_s = Some (RSt 0, v)))) →
    col !! l_s = None →
    l_t ↔h l_s -∗
    na_locs π col -∗
    (∀ v_t v_s, l_t ↦t v_t -∗ l_s ↦s v_s -∗ val_rel v_t v_s -∗
        na_locs π (<[l_s := (l_t, NaExcl)]>col) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros (Hnoforks Hcol) "#[Hbij %Hidx] Hcol HWp".
    destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_update_si_strong. iIntros (??????) "($&$&$&Hσ_s&Hinv) [%HT %Hsafe]".
    iDestruct (heap_ctx_wf with "Hσ_s") as %?.
    have [?[?[[?[?[_ [?[_ [??]]]]]] _]]]:= pool_safe_safe_reach _ _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done) ltac:(done).
    iDestruct (na_bij_access with "Hinv Hbij") as (cols ? Hwf) "(Hcols&Halloc&Hclose)".
    iDestruct (ghost_map_lookup with "Hcols Hcol") as %Hcols. rewrite lookup_map_seq_0 in Hcols.
    move: (Hcols) => /(lookup_lt_Some _ _ _) ?.
    set (cols' := <[π := (<[Loc b_s o := (Loc b_t o, NaExcl)]>col)]> cols).
    opose proof* na_locs_wf_combined_state_store as Hcom; [done|done |  |done|done| |]. 2: {
      move => ??. apply: safe_reach_mono; [done|]. move => ???. apply: post_in_ectx_mono; [done|]. naive_solver.
    } { done. }
    rewrite Hcol /= in Hcom.
    iMod (alloc_rel_remove_frac (λ _, alloc_rel_pred cols') with "Halloc Hσ_s") as (v_t) "(?&?&?&?&Hheap)".
    { done. }
    { rewrite /alloc_rel_pred => q. by erewrite Hcom. }
    { by rewrite /alloc_rel_pred combine_na_locs_list_insert //= Hcom. }
    { move => q o' ? /=. rewrite /alloc_rel_pred combine_na_locs_list_partial_alter_ne // => -[?]. done. }
    { done. }
    { done. }
    iMod (ghost_map_update with "Hcols Hcol") as "[Hcols Hcol]". rewrite insert_map_seq_0 //.
    iModIntro. iDestruct ("HWp" with "[$] [$] [$] [$]") as "$". iFrame "Hheap".
    iApply ("Hclose" with "[] [] [] [] [$] [$]"); iPureIntro.
    - by rewrite length_insert.
    - apply: na_locs_wf_insert_store; [done..| by rewrite list_insert_id | ].
      move => ?. apply: safe_reach_mono; [done|]. move => ???. apply: post_in_ectx_mono; [done|]. naive_solver.
    - move => ???? /list_lookup_insert_Some[[?[??]]|[??]] Hl'; simplify_eq; [|naive_solver].
      move: Hl' => /lookup_insert_Some[[??]|[??]]; simplify_map_eq; naive_solver.
    - move => ????. rewrite /alloc_rel_pred combine_na_locs_list_partial_alter_ne // => -[??]; simplify_eq.
  Qed.

  Lemma sim_bij_exploit_load π l_t (l_s : loc) Φ e_s e_t col:
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' σ', e' = (Load Na1Ord #l_s) ∧ ∃ n v, σ_s.(heap) !! l_s = Some (RSt n, v)))) →
    col !! l_s = None →
    l_t ↔h l_s -∗
    na_locs π col -∗
    (∀ q v_t v_s, l_t ↦t{#q} v_t -∗ l_s ↦s{#q} v_s -∗ val_rel v_t v_s -∗
        na_locs π (<[l_s := (l_t, NaRead q)]>col) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros (Hnoforks Hcol) "#[Hbij %Hidx] Hcol HWp".
    destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_update_si_strong. iIntros (??????) "($&$&$&Hσ_s&Hinv) [%HT %Hsafe]".
    iDestruct (heap_ctx_wf with "Hσ_s") as %?.
    have [?[?[[?[?[_ [_ [?[??]]]]]] _]]]:= pool_safe_safe_reach _ _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done) ltac:(done).
    iDestruct (na_bij_access with "Hinv Hbij") as (cols ? Hwf) "(Hcols&Halloc&Hclose)".
    iDestruct (ghost_map_lookup with "Hcols Hcol") as %Hcols. rewrite lookup_map_seq_0 in Hcols.
    move: (Hcols) => /(lookup_lt_Some _ _ _) ?.
    opose proof* na_locs_wf_combined_state_load as Hcom; [done|done | |done|done | |]. 2: {
      move => ??. apply: safe_reach_mono; [done|]. move => ???. apply: post_in_ectx_mono; [done|]. naive_solver.
    } { done. }
    destruct Hcom as [q Hcom]. rewrite Hcol /= in Hcom.
    set (q1 := (default 1%Qp (q ≫= (λ q', 1 - q')%Qp))).
    set (cols' := <[π := (<[Loc b_s o := (Loc b_t o, NaRead (q1 / 2)%Qp)]>col)]> cols).
    iDestruct (alloc_rel_P_holds with "Halloc Hσ_s" ) as %[q'' Hcom']; [done|].
    rewrite /alloc_rel_pred Hcom in Hcom'.
    iMod (alloc_rel_remove_frac (λ _, alloc_rel_pred cols') _ q1 (Some (q1 / 2)%Qp) ((q1 / 2))%Qp with "Halloc Hσ_s") as (v_t) "(?&?&?&?&Hheap)".
    { done. }
    { rewrite /alloc_rel_pred => q'. rewrite Hcom /q1. destruct q, q' => //= Hx. symmetry in Hx.
      by move: Hx => /Qp.sub_Some ->. }
    { rewrite /alloc_rel_pred combine_na_locs_list_insert // Hcom /=. destruct q => /=.
      - unfold q1 => /=. simplify_eq/=. destruct q'' => //; simplify_eq/=. symmetry in Hcom'.
        move: Hcom' => /Qp.sub_Some Hq. rewrite Hq /=.
        rewrite [(_/2 + _)%Qp](comm) -assoc Qp.div_2. symmetry. by apply/Qp.sub_Some.
      - by rewrite /q1 /= Qp.div_2.
    }
    { move => q' o' ? /=. rewrite /alloc_rel_pred combine_na_locs_list_partial_alter_ne // => -[?]. done. }
    { by rewrite Qp.div_2. }
    { done. }
    iMod (ghost_map_update with "Hcols Hcol") as "[Hcols Hcol]". rewrite insert_map_seq_0 //.
    iModIntro. iDestruct ("HWp" with "[$] [$] [$] [$]") as "$". iFrame "Hheap".
    iApply ("Hclose" with "[] [] [] [] [$] [$]"); iPureIntro.
    - by rewrite length_insert.
    - apply: na_locs_wf_insert_load; [done..| by rewrite list_insert_id | ].
      move => ?. apply: safe_reach_mono; [done|]. move => ???. apply: post_in_ectx_mono; [done|]. naive_solver.
    - move => ???? /list_lookup_insert_Some[[?[??]]|[??]] Hl'; simplify_eq; [|naive_solver].
      move: Hl' => /lookup_insert_Some[[??]|[??]]; simplify_map_eq; naive_solver.
    - move => ????. rewrite /alloc_rel_pred combine_na_locs_list_partial_alter_ne // => -[??]; simplify_eq.
  Qed.

  Lemma sim_bij_release ns π Φ e_s e_t col l_s l_t v_t v_s:
    let q := if ns is NaRead q then q else 1%Qp in
    col !! l_s = Some (l_t, ns) →
    l_t ↔h l_s -∗
    na_locs π col -∗
    l_t ↦t{#q} v_t -∗
    l_s ↦s{#q} v_s -∗
    val_rel v_t v_s -∗
    (na_locs π (delete l_s col) -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros (q Hl_s) "#[Hbij %Hidx] Hcol Hl_t Hl_s Hv HWp".
    destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_update_si_strong. iIntros (??????) "($&$&$&Hσ_s&Hinv) [%HT %Hsafe]".
    iDestruct (na_bij_access with "Hinv Hbij") as (cols ? Hwf) "(Hcols&Halloc&Hclose)".
    iDestruct (ghost_map_lookup with "Hcols Hcol") as %Hcols. rewrite lookup_map_seq_0 in Hcols.
    move: (Hcols) => /(lookup_lt_Some _ _ _) ?.
    set (cols' := <[π := (delete (Loc b_s o) col)]> cols).
    iMod (alloc_rel_add_frac (λ _, alloc_rel_pred cols') with "Halloc Hl_t Hl_s Hv Hσ_s") as "[? $]".
    { move => q' /=. rewrite /alloc_rel_pred (combine_na_locs_list_delete _ _ _ _ _ _ Hl_s Hcols) /=.
      rewrite -/cols' /q /combine_na_locs.
      repeat case_match; simplify_eq => //.
      - move => <-. rewrite assoc. f_equal. apply: comm.
      - by move => ->.
    }
    { move => q' o' ? /=. rewrite /alloc_rel_pred combine_na_locs_list_partial_alter_ne // => -[?]. done. }
    iMod (ghost_map_update with "Hcols Hcol") as "[Hcols Hcol]". rewrite insert_map_seq_0 //.
    iModIntro. iDestruct ("HWp" with "[$]") as "$".
    iApply ("Hclose" with "[] [] [] [] [$] [$]"); iPureIntro.
    - by rewrite length_insert.
    - by apply: na_locs_wf_delete.
    - move => ???? /list_lookup_insert_Some[[?[??]]|[??]] Hl'; simplify_eq; [|naive_solver].
      move: Hl' => /lookup_delete_Some[??]; simplify_eq; naive_solver.
    - move => ????. rewrite /alloc_rel_pred combine_na_locs_list_partial_alter_ne // => -[??]; simplify_eq.
  Qed.

  Lemma sim_bij_store_na π l_t l_s v_t v_s Φ col :
    col !! l_s = None →
    l_t ↔h l_s -∗
    na_locs π col -∗
    val_rel v_t v_s -∗
    (na_locs π col -∗ #() ⪯{π} #() [{ Φ }]) -∗
    Store Na1Ord (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯{π} Store Na1Ord (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof.
    iIntros (?) "#Hbij Hc Hv Hsim".
    iApply (sim_bij_exploit_store with "Hbij Hc"); [|done|].
    { intros. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    iIntros (v_t' v_s') "Hlt Hls Hv' Hc".
    iApply source_red_sim_expr.
    iApply (source_red_store_na with "Hls"). iIntros "Hls".
    iApply source_red_base. iModIntro.
    iApply target_red_sim_expr.
    iApply (target_red_store_na with "Hlt"). iIntros "Hlt".
    iApply target_red_base. iModIntro.
    iApply (sim_bij_release NaExcl with "Hbij Hc Hlt Hls Hv"); [by simplify_map_eq|].
    iIntros "Hc". rewrite delete_insert_id //. by iApply "Hsim".
  Qed.

  Lemma sim_bij_store_sc K_t K_s π l_t l_s v_t v_s Φ col :
    col !! l_s = None →
    (∀ (l_s' : loc) l_t' ns P_s σ_s,
        col !! l_s' = Some (l_t', ns) →
        safe_reach P_s (fill K_s #()) σ_s (post_in_ectx (λ e' σ', ∃ v' : val, e' = (if ns is NaExcl then Store Na1Ord #l_s' v' else Load Na1Ord #l_s')))) →
    l_t ↔h l_s -∗
    na_locs π col -∗
    val_rel v_t v_s -∗
    (na_locs π col -∗ fill K_t #() ⪯{π} fill K_s #() [{ Φ }]) -∗
    fill K_t (Store ScOrd (Val $ LitV (LitLoc l_t)) (Val v_t)) ⪯{π} fill K_s (Store ScOrd (Val $ LitV (LitLoc l_s)) (Val v_s)) [{ Φ }].
  Proof.
    iIntros (Hl Hcol) "#[Hbij %Hidx] Hcol Hv Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_prim_step_both.
    iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [%HT %Hsafe]]".
    iDestruct (heap_ctx_wf with "Hσ_s") as %?.
    rewrite fill_comp in HT.
    have [m[?[[<-]?]]]:= pool_safe_implies Hsafe ltac:(done).
    iDestruct (na_bij_access with "Hinv Hbij") as (cols ? Hwf) "(Hcols&Halloc&Hclose)".

    iDestruct (ghost_map_lookup with "Hcols Hcol") as %Hcoll.
    rewrite lookup_map_seq_0 in Hcoll.
    opose proof* na_locs_wf_combined_state_store as Hcom; [done|done | |done|done | |]; simplify_map_eq.
    2: { intros. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    { done. }
    iDestruct (alloc_rel_read true with "Halloc Hσ_s Hσ_t") as (st' v' ? ?) "#Hv'"; [done| |]; simplify_eq.
    { move => ?. rewrite /alloc_rel_pred /= Hcom; naive_solver. }

    iModIntro; iSplit.
    { iPureIntro. eexists _, _, _. apply: fill_prim_step. apply: base_prim_step. by econstructor. }
    iIntros (e_t' efs σ_t' [?[??]]%base_reducible_prim_step_ctx); [|by eauto with base_step]; inv_base_step.
    iMod (alloc_rel_write with "Halloc Hσ_s Hσ_t Hv") as "(Halloc&Hσ_t&Hσ_s)"; [done| |].
    { move => ?. by rewrite /alloc_rel_pred /= Hcom. }
    iModIntro. iExists _, _, _.
    iSplitR.
    { iPureIntro. apply: fill_prim_step. apply: base_prim_step. by econstructor. }
    iDestruct ("Hsim" with "Hcol") as "$".
    iFrame "HP_t HP_s Hσ_t Hσ_s" => /=. rewrite !right_id.
    iApply ("Hclose" with "[%] [%] [%] [%] Hcols Halloc").
    - by rewrite length_insert.
    - rewrite fill_comp. apply: (na_locs_wf_store σ_s); [done |done | | done | done | done | done | done ].
      right. split; [done|]. move => ?????. rewrite -fill_comp. apply: fill_safe_reach. naive_solver.
    - naive_solver.
    - naive_solver.
  Qed.

  Lemma sim_bij_store_sc_empty π l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    na_locs π ∅ -∗
    val_rel v_t v_s -∗
    (na_locs π ∅ -∗ #() ⪯{π} #() [{ Φ }]) -∗
    (Store ScOrd (Val $ LitV (LitLoc l_t)) (Val v_t)) ⪯{π} (Store ScOrd (Val $ LitV (LitLoc l_s)) (Val v_s)) [{ Φ }].
  Proof.
    iIntros "????". rewrite -(fill_empty (Store _ #l_t _)) -(fill_empty (Store _ #l_s _)).
    iApply (sim_bij_store_sc with "[$] [$] [$]"); [done|done|].
     by rewrite !fill_empty.
  Qed.

  Lemma sim_bij_store_sc_source π l_s v_s v_s' Φ :
    l_s ↦s v_s' -∗
    na_locs π ∅ -∗
    (na_locs π ∅ -∗ l_s ↦s v_s -∗ source_red (of_val #()) π Φ) -∗
    source_red (Store ScOrd (Val $ LitV (LitLoc l_s)) (Val v_s)) π Φ.
  Proof.
    iIntros "Hl Hc Hsim". iApply source_red_lift_base_step.
    iIntros (P_s σ_s ????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]] !>".
    iDestruct (heap_ctx_wf with "Hσ_s") as %?.
    iDestruct (heap_read_1 with "Hσ_s Hl") as %?.
    iExists _, _. iSplit; [iPureIntro; by econstructor|].
    iMod (heap_write with "Hσ_s Hl") as "[$ ?]".
    iFrame. iModIntro.
    iDestruct "Hinv" as "(%L&%cols&%Hlen&%Hwf&?&Hcols&?)".
    iDestruct (ghost_map_lookup with "Hcols Hc") as %Hcoll.
    rewrite lookup_map_seq_0 in Hcoll.
    iDestruct ("Hsim" with "Hc [$]") as "$". iExists _, _. iFrame.
    iPureIntro. rewrite length_insert. split; [done|].
    apply: na_locs_wf_store; [done | done | by right | done | done | done | done |done].
  Qed.

  Lemma sim_bij_load_na π l_t l_s Φ col :
    col !! l_s = None →
    l_t ↔h l_s -∗
    na_locs π col -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ na_locs π col -∗ v_t ⪯{π} v_s [{ Φ }]) -∗
    Load Na1Ord (Val $ LitV (LitLoc l_t)) ⪯{π} Load Na1Ord (Val $ LitV (LitLoc l_s)) [{ Φ }].
  Proof.
    iIntros (?) "#Hbij Hc Hsim".
    iApply (sim_bij_exploit_load with "Hbij Hc"); [|done|].
    { intros. apply: safe_reach_safe_implies => ?. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    iIntros (q v_t v_s) "Hlt Hls #Hv Hc".
    iApply source_red_sim_expr.
    iApply (source_red_load_na with "Hls"). iIntros "Hls".
    iApply source_red_base. iModIntro.
    iApply target_red_sim_expr.
    iApply (target_red_load_na with "Hlt"). iIntros "Hlt".
    iApply target_red_base. iModIntro.
    iApply (sim_bij_release (NaRead _) with "Hbij Hc Hlt Hls Hv"); [by simplify_map_eq|].
    iIntros "Hc". rewrite delete_insert_id //. by iApply "Hsim".
  Qed.

  Lemma sim_bij_load_sc π l_t l_s Φ col :
    col !! l_s = None →
    l_t ↔h l_s -∗
    na_locs π col -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ na_locs π col -∗ v_t ⪯{π} v_s [{ Φ }]) -∗
    Load ScOrd (Val $ LitV (LitLoc l_t)) ⪯{π} Load ScOrd (Val $ LitV (LitLoc l_s)) [{ Φ }].
  Proof.
    iIntros (Hcol) "#[Hbij %Hidx] Hcol Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_base_step_both.
    iIntros (P_t P_s σ_t σ_s ??) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [m[?[?[[<-]?]]]]:= pool_safe_implies Hsafe ltac:(done).
    iDestruct (na_bij_access with "Hinv Hbij") as (cols ? Hwf) "(Hcols&Halloc&Hclose)".

    iDestruct (ghost_map_lookup with "Hcols Hcol") as %Hcoll.
    rewrite lookup_map_seq_0 in Hcoll.
    opose proof* na_locs_wf_combined_state_load as Hcom; [done|done | |done|done | |]; simplify_map_eq.
    2: { intros. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
    { done. }
    destruct Hcom as [q Hcom].
    iDestruct (alloc_rel_read false with "Halloc Hσ_s Hσ_t") as (st' v' ? Hst) "#Hv'"; [done| |].
    { move => q'. rewrite /alloc_rel_pred /= Hcom; destruct q, q' => //=; naive_solver. }
    destruct Hst; simplify_eq.

    iModIntro; iSplit; first by eauto with base_step.
    iIntros (e_t' efs σ_t') "%"; inv_base_step.
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with base_step.
    iDestruct ("Hsim" with "Hv' Hcol") as "$".
    iFrame "HP_t HP_s Hσ_t Hσ_s" => /=. rewrite !right_id.
    iApply ("Hclose" with "[%] [%] [%] [%] Hcols Halloc").
    - by rewrite length_insert.
    - apply: (na_locs_wf_load σ_s); [done |done | done | done | done | done ].
    - naive_solver.
    - naive_solver.
  Qed.

  Lemma sim_bij_load π l_t l_s Φ col o :
    col !! l_s = None →
    o ≠ Na2Ord →
    l_t ↔h l_s -∗
    na_locs π col -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ na_locs π col -∗ v_t ⪯{π} v_s [{ Φ }]) -∗
    Load o (Val $ LitV (LitLoc l_t)) ⪯{π} Load o (Val $ LitV (LitLoc l_s)) [{ Φ }].
  Proof.
    move => ??. destruct o => //.
    - by apply: sim_bij_load_sc.
    - by apply: sim_bij_load_na.
  Qed.

  Lemma sim_bij_free π l_t l_s Φ n col:
    (∀ i, (0 ≤ i < n)%Z → col !! (l_s +ₗ i) = None) →
    l_t ↔h l_s -∗
    na_locs π col -∗
    (na_locs π col -∗ #() ⪯{π} #() [{ Φ }]) -∗
    FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l_t) ⪯{π} FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l_s) [{ Φ }].
  Proof.
    iIntros (Hcol) "#[Hbij %Hidx] Hcol Hsim". destruct l_s as [b_s o], l_t as [b_t o']; simplify_eq/=.
    iApply sim_lift_base_step_both.
    iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %Hsafe]]".
    have [m[?[[<-][[<-][?[??]]]]]]:= pool_safe_implies Hsafe ltac:(done).
    iDestruct (na_bij_access with "Hinv Hbij") as (cols ? Hwf) "(Hcols&Halloc&Hclose)".
    iDestruct (ghost_map_lookup with "Hcols Hcol") as %Hcoll.
    rewrite lookup_map_seq_0 in Hcoll.
    iMod (alloc_rel_free with "Halloc Hσ_s Hσ_t") as (??) "(Halloc & Hσ_s & Hσ_t)"; [done|done| done | |].
    { move => ? k ?. rewrite /alloc_rel_pred.
      change (Loc b_s k) with (Loc b_s 0 +ₗ k).
      erewrite na_locs_wf_combined_state_Free; [|done..| ].
      2: { intros. apply: safe_reach_refl. apply: post_in_ectx_intro. naive_solver. }
      by rewrite Hcol. }

    iModIntro; iSplit; first by eauto with base_step lia.
    iIntros (e_t' efs σ_t') "%"; inv_base_step.
    iModIntro. iExists _, _, _.
    iSplitR; first by eauto with base_step.
    iDestruct ("Hsim" with "Hcol") as "$". iFrame "HP_t HP_s Hσ_t Hσ_s". iSplit; [|done].
    iApply ("Hclose" with "[%] [%] [%] [%] [$] [$]").
    - rewrite length_app length_insert /=. lia.
    - rewrite app_nil_r. by apply: na_locs_wf_free.
    - naive_solver.
    - naive_solver.
  Qed.

  Lemma sim_bij_fork π e_t e_s Ψ :
    na_locs π ∅ -∗
    (na_locs π ∅ -∗ #() ⪯{π} #() [{ Ψ }]) -∗
    (∀ π', na_locs π' ∅ -∗ e_t ⪯{π'} e_s [{ lift_post (λ vt vs, na_locs π' ∅ ∗ val_rel vt vs) }]) -∗
    Fork e_t ⪯{π} Fork e_s [{ Ψ }].
  Proof.
    iIntros "Hc Hval Hsim". iApply sim_lift_base_step_both.
    iIntros (P_t P_s σ_t σ_s T_s K_s) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]] !>".
    iSplitR. { eauto with base_step. }
    iIntros (e_t' efs_t σ_t') "%"; inv_base_step.
    iExists _, _, _. iSplitR. { eauto with base_step. }
    simpl. iFrame.
    iDestruct "Hinv" as (L cols Hlen Hwf ?) "(Hcols&[Hb HL]&Hgs)".
    iMod (ghost_map_insert (length T_s) ∅ with "Hcols") as "[Hcols Hcol']".
    { apply lookup_map_seq_None. lia. }
    rewrite -Hlen -(map_seq_snoc 0).
    iDestruct (ghost_map_lookup with "Hcols Hc") as %Hempty.
    rewrite lookup_map_seq_0 lookup_app_l in Hempty.
    2: { rewrite Hlen. by apply: lookup_lt_Some. }
    iDestruct ("Hval" with "Hc") as "$".
    iSplitR "Hsim Hcol'"; last first.
    { iModIntro. iSplit; [|done]. iApply "Hsim". by rewrite Nat.add_0_r. }
    iExists _, _. iFrame. iModIntro.
    repeat iSplit; try iPureIntro.
    - rewrite !length_app length_insert /=. lia.
    - by apply na_locs_wf_fork.
    - move => ???? /lookup_app_Some[?|[??]]; [naive_solver|]. by simplify_list_eq.
    - iApply (big_sepS_impl with "HL").
      iIntros "!>" ([??] ?) "Hrel".
      iApply (alloc_rel_mono with "Hrel") => /= ??.
      by rewrite /alloc_rel_pred combine_na_locs_list_snoc_empty.
  Qed.

  Lemma sim_bij_insertN π l_t l_s vs_t vs_s e_t e_s n Φ :
    n > 0 →
    length vs_t = n →
    length vs_s = n →
    †l_t …t n -∗
    †l_s …s n -∗
    l_t ↦t∗ vs_t -∗
    l_s ↦s∗ vs_s -∗
    ([∗ list] vt;vs∈vs_t;vs_s, val_rel vt vs) -∗
    (l_t ↔h l_s -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros (Hn Ht Hs) "[% Hs_t] [% Hs_s] Hl_t Hl_s Hval Hsim". iApply sim_update_si.
    iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
    iDestruct "Hinv" as (L cols ? ? HL) "(Hcols & Hbij & Hgs)".
    iMod (heapbij_insertN with "Hbij Hl_t Hl_s Hval Hs_t Hs_s") as "[Hbij #?]"; [done..| |].
    - move => o ? HLs. rewrite /alloc_rel_pred combine_na_locs_list_None //.
      move => π' cols' Hcols.
      destruct (cols' !! (l_s +ₗ o)) eqn: Hk => //.
      exfalso. have /=[??]:= HL _ _ _ _ Hcols Hk. by apply: HLs.
    - iModIntro. iDestruct ("Hsim" with "[//]") as "$". iFrame "HP_t HP_s Hσ_t Hσ_s".
      iExists _, _. iFrame. iPureIntro. split_and!; [done..|].
      by apply: na_locs_in_L_extend.
  Qed.

  Lemma sim_bij_insert π l_t l_s v_t v_s e_t e_s Φ :
    †l_t …t 1 -∗
    †l_s …s 1 -∗
    l_t ↦t v_t -∗
    l_s ↦s v_s -∗
    val_rel v_t v_s -∗
    (l_t ↔h l_s -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hs_t Hs_s Hl_t Hl_s Hv".
    iApply (sim_bij_insertN _ _ _ [v_t] [v_s] with "Hs_t Hs_s [Hl_t] [Hl_s] [Hv]"); [lia | done | done | | | ].
    - by rewrite heap_pointsto_vec_singleton.
    - by rewrite heap_pointsto_vec_singleton.
    - by iApply big_sepL2_singleton.
  Qed.

  Lemma sim_bij_freeable_ne_val l1 v_t2 v_s2 Φ n:
    val_rel v_t2 v_s2 -∗
    †l1…?s n -∗
    (⌜if v_s2 is #(LitLoc l_s2) then loc_block l1 ≠ loc_block l_s2 else True⌝ -∗ †l1…?s n -∗ Φ) -∗
    update_si Φ.
  Proof.
    iIntros "Hbij [% Hf] HΦ" (P_t σ_t P_s σ_s T_s) "($&$&$&$&Hinv)".
    iDestruct "Hinv" as (L cols ???) "(?&Hb&?)".
    case_match; [case_match|..].
    5: iDestruct (gen_val_rel_loc_source with "Hbij") as (? ->) "Hbij".
    5: iDestruct (heapbij_block_size_ne with "Hbij Hf Hb") as %?.
    all: iModIntro; iDestruct ("HΦ" with "[//] [$Hf]") as "$"; [done|].
    all: iExists _, _; by iFrame.
  Qed.

  Lemma sim_bij_freeable_ne l1 l_t2 l_s2 Φ n:
    l_t2 ↔h l_s2 -∗
    †l1…?s n -∗
    (⌜loc_block l1 ≠ loc_block l_s2⌝ -∗ †l1…?s n -∗ Φ) -∗
    update_si Φ.
  Proof. apply (sim_bij_freeable_ne_val _ (LitV $ LitLoc l_t2) (LitV $ LitLoc l_s2)). Qed.

End fix_heap.
