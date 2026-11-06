From simuliris.simulation Require Import slsls lifting gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import log_rel_structural gen_refl pure_refl wf.
From simuliris.simulang.na_inv Require Export inv.

(** * Reflexivity theorem for read only expressions *)

Definition readonly_wf (e : expr_head) : Prop :=
  match e with
  | ValHead v => val_wf v
  (* Na2Ord is an intermediate ordering that should only arise during
  execution and programs should not use it directly. *)
  | LoadHead o => o ≠ Na2Ord
  | FreeNHead | ForkHead | CallHead | StoreHead _ => False
  | _ => True
  end.

Section refl.
  Context `{naGS Σ}.

  Definition pointsto_list (ms : list (loc * loc * val * val * Qp)) : iProp Σ :=
    [∗ list] m∈ms, let '(l_t, l_s, v_t, v_s, q) := m in
     l_t↦t{#q}v_t ∗ l_s↦s{#q}v_s ∗ val_rel v_t v_s ∗ heapbij.loc_rel l_t l_s.

  Definition na_locs_in_pointsto_list (ms : list (loc * loc * val * val * Qp)) (col : gmap loc (loc * na_locs_state)) : Prop :=
    ∀ l_s l_t ns, col !! l_s = Some (l_t, ns) →
      ∃ i v_t v_s, ms !! i = Some (l_t, l_s, v_t, v_s, if ns is NaRead q then q else 1%Qp).

   Lemma sim_bij_load_pointstolist ms π l_t l_s Φ col o :
    o ≠ Na2Ord →
    na_locs_in_pointsto_list ms col →
    l_t ↔h l_s -∗
    na_locs π col -∗
    pointsto_list ms -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ na_locs π col -∗ pointsto_list ms -∗ v_t ⪯{π} v_s [{ Φ }]) -∗
    Load o (Val $ LitV (LitLoc l_t)) ⪯{π} Load o (Val $ LitV (LitLoc l_s)) [{ Φ }].
   Proof.
     iIntros (? Hin) "Hv Hc Hms HΦ".
      destruct (col !! l_s) as [[??]|] eqn:Heq.
      + move: (Hin _ _ _ Heq) => [i [v_t [v_s Hms]]].
        iDestruct (big_sepL_lookup_acc with "Hms") as "[Hl Hms]"; [done|].
        iDestruct "Hl" as "(Hl_t & Hl_s & #Hv' & Hl')".
        iDestruct (heapbij_loc_inj with "Hv Hl'") as %?; subst.
        to_source. iApply (source_red_load with "Hl_s"); [destruct o; naive_solver|]. iIntros "Hl_s".
        to_target. iApply (target_red_load with "Hl_t"); [destruct o; naive_solver|]. iIntros "Hl_t".
        to_sim. iApply ("HΦ" with "Hv' Hc").
        by iDestruct ("Hms" with "[$Hl_s $Hl_t $Hv' $Hl']") as "$".
      + iApply (sim_bij_load with "Hv Hc"); [done..|].
        iIntros (??) "H Hc". iApply ("HΦ" with "H Hc Hms").
   Qed.

  Definition readonly_thread_own ms col (π : thread_id) : iProp Σ :=
    ⌜na_locs_in_pointsto_list ms col⌝ ∗ na_locs π col ∗ pointsto_list ms.

  Theorem readonly_log_rel_structural ms col :
    log_rel_structural heapbij.loc_rel (readonly_thread_own ms col) readonly_wf.
  Proof.
    intros e_t e_s ?? Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //; simpl in Hs; simplify_eq.
    all: try by iApply pure_log_rel_structural; unfold loc_rel_func_law, loc_rel_inj_law, loc_rel_offset_law; eauto using heapbij_loc_func, heapbij_loc_inj, heapbij_loc_shift, sim_bij_contains_globalbij.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* AllocN *)
      iApply (log_rel_allocN with "IH IH1").
      iIntros (n ?????) "Ht Hv Hcont".
      target_alloc l_t as "Hl_t" "Ha_t"; first done.
      source_alloc l_s as "Hl_s" "Ha_s"; first done.
      iApply (sim_bij_insertN with "Ha_t Ha_s Hl_t Hl_s [Hv]"); [lia | by rewrite length_replicate.. | | ].
      { iDestruct "Hv" as "#Hv".
        rewrite big_sepL2_replicate_l; last by rewrite length_replicate.
        generalize (Z.to_nat n) => n'.
        iInduction n' as [] "IHn"; cbn; first done. iFrame "Hv IHn".
      }
      by iApply "Hcont".
    - (* Load *)
      simpl in Hwf. iApply (log_rel_load with "IH").
      iIntros (????) "(%Hin & Hc & Hms) Hv Hcont".
      iApply (sim_bij_load_pointstolist with "Hv Hc Hms"); [done..|].
      iIntros (??) "Hv Hc Hms". by iApply ("Hcont" with "[$Hc $Hms] Hv").
  Qed.

End refl.
