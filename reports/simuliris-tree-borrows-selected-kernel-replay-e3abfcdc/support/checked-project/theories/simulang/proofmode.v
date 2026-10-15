From iris.proofmode Require Import rocq_tactics reduction.
From iris.proofmode Require Export proofmode.
From simuliris.simulation Require Import slsls lifting language gen_log_rel.
From simuliris.simulang Require Import tactics.
From simuliris.simulang Require Export notation primitive_laws class_instances.
From iris.bi Require Import bi.

Import bi.

Section sim.
Context `{!sheapGS Σ} `{sheapInv Σ}.

Lemma tac_sim_expr_eval π Δ Φ e_t e_t' e_s e_s' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (e_t' ⪯{π} e_s' [{ Φ }]) → envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]).
Proof. by intros -> ->. Qed.

Lemma tac_target_red_expr_eval Δ Ψ e_t e_t' :
  (∀ (e_t'':=e_t'), e_t = e_t'') →
  envs_entails Δ (target_red e_t' Ψ : iProp Σ) →
  envs_entails Δ (target_red e_t Ψ).
Proof. by intros ->. Qed.

Lemma tac_source_red_expr_eval π Δ Ψ e_s e_s' :
  (∀ (e_s'':=e_s'), e_s = e_s'') →
  envs_entails Δ (source_red e_s' π Ψ : iProp Σ) →
  envs_entails Δ (source_red e_s π Ψ).
Proof. by intros ->. Qed.

Lemma tac_target_red_pure Δ n e_t e_t' K_t Ψ (ϕ : Prop):
  PureExec ϕ n (e_t) (e_t') →
  ϕ →
  envs_entails Δ (target_red (fill K_t e_t') Ψ : iProp Σ) →
  envs_entails Δ (target_red (fill K_t e_t) Ψ).
Proof.
  intros ? ?. rewrite envs_entails_unseal. intros ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  apply: target_red_lift_pure. done.
Qed.

Lemma tac_source_red_pure π Δ n e_s e_s' K_s Ψ (ϕ : Prop):
  PureExec ϕ n e_s e_s' →
  ϕ →
  envs_entails Δ (source_red (fill K_s e_s') π Ψ : iProp Σ) →
  envs_entails Δ (source_red (fill K_s e_s) π Ψ).
Proof.
  intros ? ?. rewrite envs_entails_unseal. intros ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_ctx.
  apply: source_red_lift_pure. done.
Qed.

Lemma tac_target_red_base e_t Ψ Δ :
  envs_entails Δ (|==> Ψ e_t : iProp Σ) → envs_entails Δ (target_red e_t Ψ).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". by iApply target_red_base.
Qed.
Lemma tac_target_red_base_no_bupd e_t Ψ Δ :
  envs_entails Δ (Ψ e_t : iProp Σ) → envs_entails Δ (target_red e_t Ψ).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". by iApply target_red_base.
Qed.

Lemma tac_source_red_base π e_s Ψ Δ :
  envs_entails Δ (|==> Ψ e_s : iProp Σ) → envs_entails Δ (source_red e_s π Ψ).
Proof.
  rewrite envs_entails_unseal => ->. by iApply source_red_base.
Qed.
Lemma tac_source_red_base_no_bupd π e_s Ψ Δ :
  envs_entails Δ (Ψ e_s : iProp Σ) → envs_entails Δ (source_red e_s π Ψ).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". by iApply source_red_base.
Qed.

Lemma tac_sim_value π v_t v_s (Φ : val → val → iProp Σ) Δ :
  envs_entails Δ (|==> Φ v_t v_s) → envs_entails Δ (Val v_t ⪯{π} Val v_s {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "H". iApply sim_bupd. by iApply sim_value.
Qed.

Lemma tac_sim_value_no_bupd π v_t v_s Φ Δ :
  envs_entails Δ (Φ v_t v_s) → envs_entails Δ (Val v_t ⪯{π} Val v_s {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. by iApply sim_value. Qed.

Lemma tac_sim_bind π K_t K_s Δ Φ e_t f_t e_s f_s :
  f_t = (λ e_t, fill K_t e_t) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (e_t ⪯{π} e_s {{ λ e_t' e_s', f_t e_t' ⪯{π} f_s e_s' [{ Φ }] }})%I →
  envs_entails Δ (fill K_t e_t ⪯{π} fill K_s e_s [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> -> ->. intros Hs.
  iIntros "H". iApply (sim_bind e_t e_s K_t K_s Φ). by iApply Hs.
Qed.

Lemma tac_target_red_bind K_t e_t f_t Ψ Δ :
  f_t = (λ e_t, fill K_t e_t) →
  envs_entails Δ (target_red e_t (λ e_t', target_red (f_t e_t') Ψ) : iProp Σ) →
  envs_entails Δ (target_red (fill K_t e_t) Ψ).
Proof.
  rewrite envs_entails_unseal=> ->. intros Hs.
  iIntros "H". iApply target_red_bind. by iApply Hs.
Qed.

Lemma tac_source_red_bind π K_s e_s f_s Ψ Δ :
  f_s = (λ e_s, fill K_s e_s) →
  envs_entails Δ (source_red e_s π (λ e_s', source_red (f_s e_s') π Ψ) : iProp Σ) →
  envs_entails Δ (source_red (fill K_s e_s) π Ψ).
Proof.
  rewrite envs_entails_unseal=> ->. intros Hs.
  iIntros "H". iApply source_red_bind. by iApply Hs.
Qed.

Lemma tac_target_red_allocN n v j i K Ψ Δ :
  (0 < n)%Z →
  (∀ l,
    match envs_app false (Esnoc (Esnoc Enil i († l …t Z.to_nat n)) j (l ↦t∗ (replicate (Z.to_nat n) v))) Δ with
    | Some Δ' =>
       envs_entails Δ' (target_red (fill K (Val $ LitV $ LitLoc l)) Ψ)
    | None => False
    end) →
  envs_entails Δ (target_red (fill K (AllocN (Val $ LitV $ LitInt n) (Val v))) Ψ).
Proof.
  rewrite envs_entails_unseal=> ? HΔ. iIntros "He".
  iApply target_red_bind. iApply (target_red_allocN); [done..| ].
  iIntros (l) "Hl Hn". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply target_red_base. iModIntro. iApply HΔ.
  rewrite envs_app_sound //; simpl. iApply "He"; iSplitL "Hl"; eauto.
Qed.

Lemma tac_source_red_allocN π n v j i K Ψ Δ `{!sheapInvSupportsAlloc}:
  (0 < n)%Z →
  (∀ l,
    match envs_app false (Esnoc (Esnoc Enil i (†l …s Z.to_nat n)) j (l ↦s∗ (replicate (Z.to_nat n) v))) Δ with
    | Some Δ' =>
       envs_entails Δ' (source_red (fill K (Val $ LitV $ LitLoc l)) π Ψ)
    | None => False
    end) →
  envs_entails Δ (source_red (fill K (AllocN (Val $ LitV $ LitInt n) (Val v))) π Ψ).
Proof.
  rewrite envs_entails_unseal=> ? HΔ. iIntros "He".
  iApply source_red_bind. iApply source_red_allocN; [done..| ].
  iIntros (l) "Hl Hn". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply source_red_base. iModIntro.
  iApply HΔ. rewrite envs_app_sound //; simpl. iApply "He"; iSplitL "Hl"; eauto.
Qed.

Lemma tac_target_red_alloc v j i K Ψ Δ:
  (∀ l,
    match envs_app false (Esnoc (Esnoc Enil i (†l …t 1)) j (l ↦t v)) Δ with
    | Some Δ' =>
       envs_entails Δ' (target_red (fill K (Val $ LitV $ LitLoc l)) Ψ)
    | None => False
    end) →
  envs_entails Δ (target_red (fill K (Alloc (Val v))) Ψ).
Proof.
  rewrite envs_entails_unseal=> HΔ. iIntros "He".
  iApply target_red_bind. iApply target_red_alloc.
  iIntros (l) "Hl Hn". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply target_red_base. iModIntro.
  iApply HΔ. rewrite envs_app_sound //; simpl. iApply "He"; iSplitL "Hl"; eauto.
Qed.

Lemma tac_source_red_alloc π v j i K Ψ Δ `{!sheapInvSupportsAlloc}:
  (∀ l,
    match envs_app false (Esnoc (Esnoc Enil i (†l …s 1)) j (l ↦s v)) Δ with
    | Some Δ' =>
       envs_entails Δ' (source_red (fill K (Val $ LitV $ LitLoc l)) π Ψ)
    | None => False
    end) →
  envs_entails Δ (source_red (fill K (Alloc (Val v))) π Ψ).
Proof.
  rewrite envs_entails_unseal=> HΔ. iIntros "He".
  iApply source_red_bind. iApply source_red_alloc.
  iIntros (l) "Hl Hn". specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  iApply source_red_base. iModIntro.
  iApply HΔ. rewrite envs_app_sound //; simpl. iApply "He"; iSplitL "Hl"; eauto.
Qed.

Lemma tac_target_red_free l v i j K Ψ Δ Δ':
  envs_lookup_delete false i Δ = Some (false, l ↦t v, Δ')%I →
  envs_lookup j Δ' = Some (false, †l …t 1)%I →
  (let Δ'' := envs_delete false j false Δ' in
    envs_entails Δ'' (target_red (fill K (Val $ LitV LitUnit)) Ψ)) →
  envs_entails Δ (target_red (fill K (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV $ LitLoc l))) Ψ).
Proof.
  rewrite envs_entails_unseal. rewrite envs_lookup_delete_Some. intros [Hlk ->] Hn Hfin.
  rewrite -target_red_bind.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hlk]; simpl.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hn]; simpl.
  rewrite Hfin.
  iIntros "(Hv & Ha & Hs)". iApply (target_red_free with "Hv Ha").
  iIntros "_". (* TODO: DON'T DROP THIS! *)
  by iApply target_red_base.
Qed.

Lemma tac_source_red_free π l v i j K Ψ Δ Δ' `{!sheapInvSupportsFree}:
  envs_lookup_delete false i Δ = Some (false, l ↦s v, Δ')%I →
  envs_lookup j Δ' = Some (false, †l …s 1)%I →
  (let Δ'' := envs_delete false j false Δ' in
    envs_entails Δ'' (source_red (fill K (Val $ LitV LitUnit)) π Ψ)) →
  envs_entails Δ (source_red (fill K (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV $ LitLoc l))) π Ψ).
Proof.
  rewrite envs_entails_unseal. rewrite envs_lookup_delete_Some. intros [Hlk ->] Hn Hfin.
  rewrite -source_red_bind.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hlk]; simpl.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hn]; simpl.
  rewrite Hfin.
  iIntros "(Hv & Ha & Hs)". iApply (source_red_free with "Hv Ha").
  iIntros "_". (* TODO: DON'T DROP THIS! *)
  by iApply source_red_base.
Qed.

Lemma tac_target_red_freeN l (n : Z) vs i j K Ψ Δ Δ':
  n = length vs →
  envs_lookup_delete false i Δ = Some (false, l ↦t∗ vs, Δ')%I →
  envs_lookup j Δ' = Some (false, †l …t Z.to_nat n)%I →
  (let Δ'' := envs_delete false j false Δ' in
    envs_entails Δ'' (target_red (fill K (Val $ LitV LitUnit)) Ψ)) →
  envs_entails Δ (target_red (fill K (FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l))) Ψ).
Proof.
  rewrite envs_entails_unseal. rewrite envs_lookup_delete_Some. intros Heq [Hlk ->] Hn Hfin.
  rewrite -target_red_bind.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hlk]; simpl.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hn]; simpl.
  rewrite Hfin.
  iIntros "(Hv & Ha & Hs)". iApply (target_red_freeN with "Hv Ha"); first done.
  iIntros "_". (* TODO: DON'T DROP THIS! *)
  by iApply target_red_base.
Qed.

Lemma tac_source_red_freeN π l (n : Z) vs i j K Ψ Δ Δ' `{!sheapInvSupportsFree}:
  n = length vs →
  envs_lookup_delete false i Δ = Some (false, l ↦s∗ vs, Δ')%I →
  envs_lookup j Δ' = Some (false, †l …s Z.to_nat n)%I →
  (let Δ'' := envs_delete false j false Δ' in
    envs_entails Δ'' (source_red (fill K (Val $ LitV LitUnit)) π Ψ)) →
  envs_entails Δ (source_red (fill K (FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l))) π Ψ).
Proof.
  rewrite envs_entails_unseal. rewrite envs_lookup_delete_Some. intros Heq [Hlk ->] Hn Hfin.
  rewrite -source_red_bind.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hlk]; simpl.
  rewrite (envs_lookup_sound' _ false _ false); [ | apply Hn]; simpl.
  rewrite Hfin.
  iIntros "(Hv & Ha & Hs)". iApply (source_red_freeN with "Hv Ha"); first done.
  iIntros "_". (* TODO: DON'T DROP THIS! *)
  by iApply source_red_base.
Qed.

Lemma target_red_load o l q v Ψ:
  o = ScOrd ∨ o = Na1Ord →
  l ↦t{#q} v -∗
  (l ↦t{#q} v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load o (Val $ LitV $ LitLoc l)) Ψ.
Proof. intros [-> | ->]; [iApply target_red_load_sc | iApply target_red_load_na]. Qed.
Lemma tac_target_red_loadsc Δ i K b l q v Ψ:
  envs_lookup i Δ = Some (b, l ↦t{#q} v)%I →
  envs_entails Δ (target_red (fill K (Val v)) Ψ) →
  envs_entails Δ (target_red (fill K (Load ScOrd (LitV l))) Ψ).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -target_red_bind. eapply wand_apply; first by apply bi.wand_entails, target_red_load_sc.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply target_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * apply sep_mono_r, wand_mono; first done. rewrite Hi. iIntros "Ht".
    iApply target_red_base; eauto.
Qed.
Lemma tac_target_red_loadna Δ i K b l v Ψ q:
  envs_lookup i Δ = Some (b, l ↦t{#q} v)%I →
  envs_entails Δ (target_red (fill K (Val v)) Ψ) →
  envs_entails Δ (target_red (fill K (Load Na1Ord (LitV l))) Ψ).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -target_red_bind. eapply wand_apply; first by apply bi.wand_entails, target_red_load_na.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply target_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * apply sep_mono_r, wand_mono; first done. rewrite Hi. iIntros "Ht".
    iApply target_red_base; eauto.
Qed.

Lemma source_red_load π o l q v Ψ `{!sheapInvSupportsLoad o}:
  o = ScOrd ∨ o = Na1Ord →
  l ↦s{#q} v -∗
  (l ↦s{#q} v -∗ source_red (of_val v) π Ψ) -∗
  source_red (Load o (Val $ LitV $ LitLoc l)) π Ψ.
Proof. intros [-> | ->]; [iApply source_red_load_sc | iApply source_red_load_na]. Qed.
Lemma tac_source_red_loadsc π Δ i K b l q v Ψ `{!sheapInvSupportsLoad ScOrd}:
  envs_lookup i Δ = Some (b, l ↦s{#q} v)%I →
  envs_entails Δ (source_red (fill K (Val v)) π Ψ) →
  envs_entails Δ (source_red (fill K (Load ScOrd (LitV l))) π Ψ).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -source_red_bind. eapply wand_apply; first by apply bi.wand_entails, source_red_load_sc.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply source_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * apply sep_mono_r, wand_mono; first done. rewrite Hi. iIntros "Hs".
    iApply source_red_base; eauto.
Qed.
Lemma tac_source_red_loadna π Δ i K b l v Ψ q `{!sheapInvSupportsLoad Na1Ord}:
  envs_lookup i Δ = Some (b, l ↦s{#q} v)%I →
  envs_entails Δ (source_red (fill K (Val v)) π Ψ) →
  envs_entails Δ (source_red (fill K (Load Na1Ord (LitV l))) π Ψ).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -source_red_bind. eapply wand_apply; first by apply bi.wand_entails, source_red_load_na.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply source_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * apply sep_mono_r, wand_mono; first done. rewrite Hi. iIntros "Hs".
    iApply source_red_base; eauto.
Qed.


Lemma target_red_store l v v' o Ψ:
  o = ScOrd ∨ o = Na1Ord →
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store o (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof. intros [-> | ->]; [iApply target_red_store_sc | iApply target_red_store_na]. Qed.
Lemma tac_target_red_store Δ i K l v v' o Ψ:
  o = ScOrd ∨ o = Na1Ord →
  envs_lookup i Δ = Some (false, l ↦t v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦t v')) Δ with
  | Some Δ' => envs_entails Δ' (target_red (fill K (Val $ LitV LitUnit)) Ψ)
  | None => False
  end →
  envs_entails Δ (target_red (fill K (Store o (LitV l) (Val v'))) Ψ).
Proof.
  rewrite envs_entails_unseal=> Ho ? Hi.
  destruct (envs_simple_replace _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite -target_red_bind. eapply wand_apply; first by eapply bi.wand_entails, target_red_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. apply sep_mono_r, wand_mono; first done.
  rewrite Hi. iIntros "Ht". iApply target_red_base; eauto.
Qed.

Lemma source_red_store π l v v' o Ψ `{!sheapInvSupportsStore o}:
  o = ScOrd ∨ o = Na1Ord →
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) π Ψ) -∗
  source_red (Store o (Val $ LitV (LitLoc l)) (Val v)) π Ψ.
Proof. intros [-> | ->]; [iApply source_red_store_sc | iApply source_red_store_na]. Qed.
Lemma tac_source_red_store π Δ i K l v v' o Ψ `{!sheapInvSupportsStore o}:
  o = ScOrd ∨ o = Na1Ord →
  envs_lookup i Δ = Some (false, l ↦s v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦s v')) Δ with
  | Some Δ' => envs_entails Δ' (source_red (fill K (Val $ LitV LitUnit)) π Ψ)
  | None => False
  end →
  envs_entails Δ (source_red (fill K (Store o (LitV l) (Val v'))) π Ψ).
Proof.
  rewrite envs_entails_unseal=> Ho ? Hi.
  destruct (envs_simple_replace _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite -source_red_bind. eapply wand_apply; first by eapply bi.wand_entails, source_red_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. apply sep_mono_r, wand_mono; first done.
  rewrite Hi. iIntros "Hs". iApply source_red_base; eauto.
Qed.

Lemma tac_target_red_call Δ i K b f v fn Ψ :
  envs_lookup i Δ = Some (b, f @t fn)%I →
  envs_entails Δ (target_red (fill K (apply_func fn v)) Ψ) →
  envs_entails Δ (target_red (fill K (Call (Val $ LitV $ LitFn f) (Val v))) Ψ).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -target_red_bind. eapply wand_apply; first by apply bi.wand_entails, target_red_call.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iApply target_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * rewrite Hi. iIntros "[#Hf Hs]". iSplitR; first done.
    iApply target_red_base. iSpecialize ("Hs" with "Hf"); eauto.
Qed.

Lemma tac_source_red_call π Δ i K b f v fn Ψ :
  envs_lookup i Δ = Some (b, f @s fn)%I →
  envs_entails Δ (source_red (fill K (apply_func fn v)) π Ψ) →
  envs_entails Δ (source_red (fill K (Call (Val $ LitV $ LitFn f) (Val v))) π Ψ).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -source_red_bind. eapply wand_apply; first by apply bi.wand_entails, source_red_call.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He]". iApply source_red_base. iModIntro.
    iApply Hi. iApply "He". iFrame "#".
  * rewrite Hi. iIntros "[#Hf Hs]". iSplitR; first done.
    iApply source_red_base. iSpecialize ("Hs" with "Hf"); eauto.
Qed.


(** Switching between judgments *)
Lemma tac_to_target π Δ e_t e_s Φ :
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯{π} e_s [{ Φ }]))%I →
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]).
Proof. rewrite envs_entails_unseal=> Hi. by rewrite -target_red_sim_expr. Qed.

Lemma tac_to_source π Δ e_t e_s Φ :
  envs_entails Δ (source_red e_s π (λ e_s', e_t ⪯{π} e_s' [{ Φ }]))%I →
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]).
Proof. rewrite envs_entails_unseal=> Hi. by rewrite -source_red_sim_expr. Qed.

Lemma tac_target_to_sim π Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]) →
  envs_entails Δ (target_red e_t (λ e_t', e_t' ⪯{π} e_s [{ Φ }]))%I.
Proof.
  rewrite envs_entails_unseal=> Hi. rewrite -target_red_base.
  iIntros "He". iModIntro. by iApply Hi.
Qed.

Lemma tac_source_to_sim π Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯{π} e_s [{ Φ }]) →
  envs_entails Δ (source_red e_s π (λ e_s', e_t ⪯{π} e_s' [{ Φ }]))%I.
Proof.
  rewrite envs_entails_unseal=> Hi. rewrite -source_red_base.
  iIntros "He". iModIntro. by iApply Hi.
Qed.

Lemma tac_sim_expr_to_sim π Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯{π} e_s {{ Φ }}) →
  envs_entails Δ (e_t ⪯{π} e_s [{ lift_post Φ }])%I.
Proof. done. Qed.

Lemma tac_sim_to_sim_expr π Δ e_t e_s Φ :
  envs_entails Δ (e_t ⪯{π} e_s [{ lift_post Φ }]) →
  envs_entails Δ (e_t ⪯{π} e_s {{ Φ }})%I.
Proof. done. Qed.
End sim.

(** ** automation for source_red and target_red *)
(* the proofmode works with sim_expr, not sim *)
Ltac to_sim :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim_expr _ _ _ _) => idtac
  | |- envs_entails _ (sim _ _ ?e_t ?e_s) =>
      notypeclasses refine (tac_sim_to_sim_expr _ _ e_t e_s _ _)
  | |- envs_entails _ (target_red ?e_t (λ _, sim_expr _ _ _ _ )) =>
      notypeclasses refine (tac_target_to_sim _ _ e_t _ _ _)
  | |- envs_entails _ (source_red ?e_s _ (λ _, sim_expr _ _ _ _)) =>
      notypeclasses refine (tac_source_to_sim _ _ _ e_s _ _)
  | _ => fail "not a target_red or source_red of suitable shape"
  end.

Ltac to_target :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (target_red _ _) => idtac
  | _ =>
    to_sim;
    lazymatch goal with
    | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
        notypeclasses refine (tac_to_target π _ e_t e_s Φ _)
    | _ => fail "to_target: not a sim"
    end
  end.

Ltac to_source :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (source_red _ _ _) => idtac
  | _ =>
    to_sim;
    lazymatch goal with
    | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
        notypeclasses refine (tac_to_source π _ e_t e_s Φ _)
    | _ => fail "to_source: not a sim"
    end
  end.

(** ** simple automation for evaluation *)
Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** Simplify the goal if it is [sim] of a value.
  If the postcondition already allows a bupd, do not add a second one.
  But otherwise, *do* add a bupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac sim_value_head :=
  lazymatch goal with
  | |- envs_entails _ (sim (λ _ _, bupd _) _ (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim_expr _ _ _ _) _ (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim (λ _ _, sim _ _ _ _) _ (Val _) (Val _)) =>
      eapply tac_sim_value_no_bupd
  | |- envs_entails _ (sim _ _ (Val _) (Val _)) =>
      eapply tac_sim_value
  end.

(* TODO: do we even need this? *)
Tactic Notation "sim_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Φ ?π ?e_t ?e_s) =>
    notypeclasses refine (tac_sim_expr_eval π _ _ e_t _ e_s _ _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl | ]
  | _ => fail "sim_expr_eval: not a 'sim"
  end.
Ltac sim_expr_simpl := sim_expr_eval simpl.

(* finish and switch back to a sim, if possible *)
Ltac sim_finish :=
  try sim_expr_simpl;      (* simplify occurences of subst/fill *)
  match goal with
  | |- envs_entails _ (sim_expr (lift_post _) _ ?e_t ?e_s) =>
      notypeclasses refine (tac_sim_expr_to_sim _ _ e_t e_s _ _)
  | |- envs_entails _ (sim_expr _ _ _ _) => idtac
  | |- envs_entails _ (sim _ _ _ _) => idtac
  end;
  pm_prettify.        (* prettify λs caused by wp_value *)

(** target_red *)
Tactic Notation "target_red_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t ?Ψ) =>
    notypeclasses refine (tac_target_red_expr_eval _ _ e_t _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl| ]
  | _ => fail "target_red_expr_eval: not a 'target_red"
  end.
Ltac target_expr_simpl := target_red_expr_eval simpl; simpl_subst.

Ltac target_value_head :=
  lazymatch goal with
  | |- envs_entails _ (target_red (Val _) (λ _, bupd _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, sim_expr _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, sim _ _ _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) (λ _, target_red _ _)) =>
      eapply tac_target_red_base_no_bupd
  | |- envs_entails _ (target_red (Val _) _) =>
      eapply tac_target_red_base
  end.

Ltac target_finish :=
  target_expr_simpl;      (* simplify occurences of subst/fill *)
  first [target_value_head; try sim_finish | pm_prettify].

(** source_red *)
Tactic Notation "source_red_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s ?π ?Ψ) =>
    notypeclasses refine (tac_source_red_expr_eval _ _ _ e_s _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl| ]
  | _ => fail "source_red_expr_eval: not a 'target_red"
  end.
Ltac source_expr_simpl := source_red_expr_eval simpl; simpl_subst.

Ltac source_value_head :=
  lazymatch goal with
  | |- envs_entails _ (source_red (Val _) _ (λ _, bupd _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ (λ _, sim_expr _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ (λ _, sim _ _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ (λ _, source_red _ _ _)) =>
      eapply tac_source_red_base_no_bupd
  | |- envs_entails _ (source_red (Val _) _ _) =>
      eapply tac_source_red_base; try iIntros (_ _)
  end.

Ltac source_finish :=
  source_expr_simpl;      (* simplify occurences of subst/fill *)
  first [source_value_head; try sim_finish | pm_prettify].

(* Note: this is not called automatically by the sim_finish tactical because
   that would make it impossible to do things that need access to the SI (like updating the heap bijection).
  NOTE: alternatively, have some fancier update modality that wraps an [update_si]?
 *)
Ltac sim_val := sim_finish; sim_value_head.

(** ** Pure reduction *)

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "target_pure" open_constr(efoc) :=
  iStartProof;
  to_target;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t _) =>
    let e_t := eval simpl in e_t in
    reshape_expr e_t ltac:(fun K_t e_t' =>
      unify e_t' efoc;
      eapply (tac_target_red_pure _ _ e_t' _ K_t _ _);
      [ tc_solve                       (* PureExec *)
      | try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      | target_finish                      (* new goal *)
      ])
    || fail "target_red_pure: cannot find" efoc "in" e_t "or" efoc "is not a redex"
  | _ => fail "target_red_pure: not a 'target_red"
  end.

(** We have not declared an instance for the reduction of while:
  usually, we do not want to reduce it arbitrarily, but instead do an induction. *)
Tactic Notation "target_while" :=
  let Hwhile := fresh "H" in
  pose (Hwhile := pure_while);
  target_pure (While _ _);
  clear Hwhile.

Tactic Notation "target_if" := target_pure (If _ _ _).
Tactic Notation "target_if_true" := target_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "target_if_false" := target_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "target_unop" := target_pure (UnOp _ _).
Tactic Notation "target_binop" := target_pure (BinOp _ _ _).
Tactic Notation "target_op" := target_unop || target_binop.
Tactic Notation "target_let" := target_pure (Let (BNamed _) _ _).
Tactic Notation "target_seq" := target_pure (Let BAnon _ _).
Tactic Notation "target_proj" := target_pure (Fst _) || target_pure (Snd _).
Tactic Notation "target_match" := target_pure (Match _ _ _ _ _).
Tactic Notation "target_inj" := target_pure (InjL _) || target_pure (InjR _).
Tactic Notation "target_pair" := target_pure (Pair _ _).

Ltac target_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (target_pure _; [])
        | target_finish (* In case target_pure never ran, make sure we do the usual cleanup.*)
        ].

Tactic Notation "source_pure" open_constr(efoc) :=
  iStartProof;
  to_source;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s _ _) =>
    let e_s := eval simpl in e_s in
    reshape_expr e_s ltac:(fun K_s e_s' =>
      unify e_s' efoc;
      eapply (tac_source_red_pure _ _ _ e_s' _ K_s _ _);
      [ tc_solve                       (* PureExec *)
      | try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      | source_finish                      (* new goal *)
      ])
    || fail "source_red_pure: cannot find" efoc "in" e_s "or" efoc "is not a redex"
  | _ => fail "source_red_pure: not a 'sim'"
  end.

Tactic Notation "source_while" :=
  let Hwhile := fresh "H" in
  pose (Hwhile := pure_while);
  source_pure (While _ _);
  clear Hwhile.

Tactic Notation "source_if" := source_pure (If _ _ _).
Tactic Notation "source_if_true" := source_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "source_if_false" := source_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "source_unop" := source_pure (UnOp _ _).
Tactic Notation "source_binop" := source_pure (BinOp _ _ _).
Tactic Notation "source_op" := source_unop || source_binop.
Tactic Notation "source_let" := source_pure (Let (BNamed _) _ _).
Tactic Notation "source_seq" := source_pure (Let BAnon _ _).
Tactic Notation "source_proj" := source_pure (Fst _) || source_pure (Snd _).
Tactic Notation "source_match" := source_pure (Match _ _ _ _ _).
Tactic Notation "source_inj" := source_pure (InjL _) || source_pure (InjR _).
Tactic Notation "source_pair" := source_pure (Pair _ _).

Ltac source_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (source_pure _; [])
        | source_finish (* In case source_red_pure never ran, make sure we do the usual cleanup.*)
        ].

Ltac sim_pures_int := (try target_pures); (try source_pures); try to_sim.
Ltac sim_pures := (try target_pures); (try source_pures); try (to_sim; sim_finish).



(** ** Bind tactics *)

Ltac sim_bind_core K_t K_s :=
  lazymatch eval hnf in K_t with
  | [] => lazymatch eval hnf in K_s with
          | [] => idtac
          | _ => eapply (tac_sim_bind _ K_t K_s); [simpl; reflexivity| simpl; reflexivity | ]
          end
  | _ => eapply (tac_sim_bind _ K_t K_s); [simpl; reflexivity| simpl; reflexivity | ]
  end.

Tactic Notation "sim_bind" open_constr(efoc_t) open_constr(efoc_s) :=
  iStartProof;
  to_sim;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?Q ?π ?e_t ?e_s) =>
    first [ reshape_expr e_t ltac:(fun K_t e_t' => unify e_t' efoc_t;
                                    first [ reshape_expr e_s ltac:(fun K_s e_s' => unify e_s' efoc_s; sim_bind_core K_t K_s)
                                           (* TODO: fix error handling *)
                                           | fail 1 "sim_bind: cannot find" efoc_s "in" e_s]
                                  )
          | fail 1 "sim_bind: cannot find" efoc_t "in" e_t ]
  | _ => fail "sim_bind: not a 'sim'"
  end.

Ltac target_bind_core K_t :=
  lazymatch eval hnf in K_t with
  | [] => idtac
  | _ => eapply (tac_target_red_bind K_t); [simpl; reflexivity| reduction.pm_prettify]
  end.

Tactic Notation "target_bind" open_constr(efoc_t) :=
  iStartProof;
  to_target;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e_t ?Ψ) =>
    first [ reshape_expr e_t ltac:(fun K_t e_t' => unify e_t' efoc_t;
                                    target_bind_core K_t
                                  )
          | fail 1 "target_bind: cannot find" efoc_t "in" e_t ]
  | _ => fail "target_bind: not a 'target_red'"
  end.

Ltac source_bind_core K_s :=
  lazymatch eval hnf in K_s with
  | [] => idtac
  | _ => eapply (tac_source_red_bind _ K_s); [simpl; reflexivity| reduction.pm_prettify]
  end.

Tactic Notation "source_bind" open_constr(efoc_s) :=
  iStartProof;
  to_source;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e_s ?π ?Ψ) =>
    first [ reshape_expr e_s ltac:(fun K_s e_s' => unify e_s' efoc_s;
                                    source_bind_core K_s
                                  )
          | fail 1 "source_bind: cannot find" efoc_s "in" e_s ]
  | _ => fail "source_bind: not a 'source_red'"
  end.

(** ** [apply] tactics *)

(** The tactic [target_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [target_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [target_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac target_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (target_red ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         target_bind_core K; tac_suc H)
     | _ => fail 1 "target_apply: not a 'target_red"
     end)
  |tac_fail ltac:(fun _ => target_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "target_apply: cannot apply" lem ":" P ].

Tactic Notation "target_apply" open_constr(lem) :=
  target_apply_core lem ltac:(fun H => iApplyHyp H; try target_expr_simpl)
                        ltac:(fun cont => fail).
Tactic Notation "target_smart_apply" open_constr(lem) :=
  target_apply_core lem ltac:(fun H => iApplyHyp H; try target_expr_simpl)
                        ltac:(fun cont => target_pure _; []; cont ()).

Ltac source_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (source_red ?e ?π ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         source_bind_core K; tac_suc H)
     | _ => fail 1 "source_apply: not a 'source_red"
     end)
  |tac_fail ltac:(fun _ => source_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "source_apply: cannot apply" lem ":" P ].

Tactic Notation "source_apply" open_constr(lem) :=
  source_apply_core lem ltac:(fun H => iApplyHyp H; try source_expr_simpl)
                        ltac:(fun cont => fail).
Tactic Notation "source_smart_apply" open_constr(lem) :=
  source_apply_core lem ltac:(fun H => iApplyHyp H; try source_expr_simpl)
                        ltac:(fun cont => source_pure _; []; cont ()).

Ltac sim_apply_core lem tac_suc tac_fail :=
  iStartProof;
  to_sim;
  first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (sim_expr _ ?e_t ?e_s ?Q) =>
       reshape_expr e_t ltac:(fun K_t e_t' =>
          reshape_expr e_s ltac:(fun K_s e_s' =>
            sim_bind_core K_t K_s; tac_suc H))
     | _ => fail 1 "sim_apply: not a 'sim_expr'"
     end)
  |tac_fail ltac:(fun _ => sim_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "sim_apply: cannot apply" lem ":" P ].

Tactic Notation "sim_apply" open_constr(lem) :=
  sim_apply_core lem ltac:(fun H => iApplyHyp H; try sim_expr_simpl)
                     ltac:(fun cont => fail).
Tactic Notation "sim_smart_apply" open_constr(lem) :=
  sim_apply_core lem ltac:(fun H => iApplyHyp H; try sim_expr_simpl)
                     ltac:(fun cont => sim_pures; []; cont ()).

(** ** Call automation *)
Tactic Notation "target_call" :=
  to_target;
  let solve_hasfun _ :=
    let f := match goal with |- _ = Some (_, (?f @t _)%I) => f end in
    iAssumptionCore || fail "target_call: cannot find" f "@t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_call _ _ K _ _ _ _ _))
      |fail 1 "target_call: cannot find 'Call' in" e];
    [ solve_hasfun ()
    |target_finish]
  | _ => fail "target_call: not a 'target_red'"
  end.

Tactic Notation "source_call" :=
  to_source;
  let solve_hasfun _ :=
    let f := match goal with |- _ = Some (_, (?f @s _)%I) => f end in
    iAssumptionCore || fail "source_call: cannot find" f "@s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?π ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_call _ _ _ K _ _ _ _ _))
      |fail 1 "source_call: cannot find 'Call' in" e];
    [ solve_hasfun ()
    |source_finish]
  | _ => fail "source_call: not a 'source_red'"
  end.




(** ** Heap automation *)
Tactic Notation "target_alloc" ident(l) "as" constr(H) constr(H2) :=
  to_target;
  let Htmp := iFresh in
  let Htmp2 := iFresh in
  let finish _ :=
    first [intros l | fail 1 "target_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "target_alloc:" H " or " H2 "not fresh"
    | _ => iDestructHyp Htmp as H; iDestructHyp Htmp2 as H2; target_finish
    end in
  target_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_target_red_alloc].
     If that fails, it tries to use the lemma [tac_target_red_allocN]
     for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦t∗ [v] instead of
     l ↦t v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_alloc _ Htmp Htmp2 K _ _))
          |fail 1 "target_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_allocN _ _ Htmp Htmp2 K _ _))
          |fail 1 "target_alloc: cannot find 'AllocN' in" e];
        [idtac|finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "target_alloc: not a 'target_red'"
  end.

Tactic Notation "target_alloc" ident(l) :=
  target_alloc l as "?" "?".

Tactic Notation "source_alloc" ident(l) "as" constr(H) constr(H2) :=
  to_source;
  let Htmp := iFresh in
  let Htmp2 := iFresh in
  let finish _ :=
    first [intros l | fail 1 "source_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "source_alloc:" H " or " H2 "not fresh"
    | _ => iDestructHyp Htmp as H; iDestructHyp Htmp2 as H2; source_finish
    end in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?π ?Ψ) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_alloc _ _ Htmp Htmp2 K _ _))
          |fail 1 "source_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_allocN _ _ _ Htmp Htmp2 K _ _))
          |fail 1 "source_alloc: cannot find 'Alloc' in" e];
        [idtac|finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "source_alloc: not a 'source_red'"
  end.

Tactic Notation "source_alloc" ident(l) :=
  source_alloc l as "?" "?".

Tactic Notation "target_free" :=
  to_target;
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦t{#_} _)%I, _) => l end in
    iAssumptionCore || fail "target_free: cannot find" l "↦t ?" in
  let solve_pointstoN _ :=
    let l := match goal with |- _ = Some (_, (?l ↦t∗{#_} _)%I, _) => l end in
    iAssumptionCore || fail "target_free: cannot find" l "↦t∗ ?" in
  let solve_perm _ :=
    let l := match goal with |- _ = Some (_, († ?l …?t _)%I) => l end in
    iAssumptionCore || fail "target_free: cannot find" l "==>t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    let process_single _ :=
      first
        [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_free _ _ _ _ K _ _ _))
        |fail 1 "target_free: cannot find 'Free' in" e];
      [solve_pointsto () | solve_perm () | pm_reduce; target_finish]
    in
    let process_array _ :=
      first
        [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_freeN _ _ _ _ _ K _ _ _))
        |fail 1 "target_free: cannot find 'FreeN' in" e];
      [ | solve_pointstoN () | solve_perm () | pm_reduce; target_finish]
    in (process_single ()) || (process_array ())
  | _ => fail "target_free: not a 'target_red'"
  end.

Tactic Notation "source_free" :=
  to_source;
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦s{#_} _)%I, _) => l end in
    iAssumptionCore || fail "source_free: cannot find" l "↦s ?" in
  let solve_pointstoN _ :=
    let l := match goal with |- _ = Some (_, (?l ↦s∗{#_} _)%I, _) => l end in
    iAssumptionCore || fail "source_free: cannot find" l "↦s∗ ?" in
  let solve_perm _ :=
    let l := match goal with |- _ = Some (_, († ?l …?s _)%I) => l end in
    iAssumptionCore || fail "source_free: cannot find" l "==>s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?π ?Ψ) =>
    let process_single _ :=
      first
        [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_free _ _ _ _ _ K Ψ _ _))
        |fail 1 "source_free: cannot find 'Free' in" e];
      [solve_pointsto () | solve_perm () | pm_reduce; source_finish]
    in
    let process_array _ :=
      first
        [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_freeN _ _ _ _ _ _ K Ψ _ _))
        |fail 1 "source_free: cannot find 'FreeN' in" e];
      [idtac| solve_pointstoN () | solve_perm () | pm_reduce; source_finish]
    in (process_single ()) || (process_array ())
  | _ => fail "source_free: not a 'source_red'"
  end.

Tactic Notation "target_load" :=
  to_target;
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦t{#_} _)%I) => l end in
    iAssumptionCore || fail "target_load: cannot find" l "↦t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_loadsc _ _ K _ _ _ _ Ψ))
      |reshape_expr e ltac:(fun K e' => eapply (tac_target_red_loadna _ _ K _ _ _ Ψ _))
      |fail 1 "target_load: cannot find 'Load' in" e];
    [ solve_pointsto ()
    | target_finish]
  | _ => fail "target_load: not a 'target_red'"
  end.

Tactic Notation "source_load" :=
  to_source;
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦s{#_} _)%I) => l end in
    iAssumptionCore || fail "source_load: cannot find" l "↦s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?π ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_loadsc _ _ _ K _ _ _ _ Ψ))
      |reshape_expr e ltac:(fun K e' => eapply (tac_source_red_loadna _ _ _ K _ _ _ Ψ _))
      |fail 1 "source_load: cannot find 'Load' in" e];
    [ solve_pointsto ()
    | source_finish]
  | _ => fail "source_load: not a 'source_red'"
  end.


(* FIXME: error messages seem broken (already the eapply seems to fail when the pointsto-assumption is missing)*)
Tactic Notation "target_store" :=
  to_target;
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦t{#_} _)%I) => l end in
    iAssumptionCore || fail "target_store: cannot find" l "↦t ?" in
  target_pures;
  lazymatch goal with
  | |- envs_entails _ (target_red ?e ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_target_red_store _ _ K _ _ _ _ Ψ))
      |fail 1 "target_store: cannot find 'Store' in" e];
    [first [left; reflexivity | right; reflexivity ]
    |solve_pointsto ()
    |pm_reduce; target_finish]
  | _ => fail "target_store: not a 'target_red'"
  end.

Tactic Notation "source_store" :=
  to_source;
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦s{#_} _)%I) => l end in
    iAssumptionCore || fail "source_store: cannot find" l "↦s ?" in
  source_pures;
  lazymatch goal with
  | |- envs_entails _ (source_red ?e ?π ?Ψ) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_source_red_store _ _ _ K _ _ _ _ Ψ))
      |fail 1 "source_store: cannot find 'Store' in" e];
    [first [left; reflexivity | right; reflexivity]
    |solve_pointsto ()
    |pm_reduce; source_finish]
  | _ => fail "source_store: not a 'source_red'"
  end.


(** ** Automation related to stuckness *)

(* FIXME: currently quite tailored to the sideconditions generated by the instances we already have.
  Maybe we can make this more general? *)
Ltac source_stuck_sidecond :=
  unfold bin_op_eval, un_op_eval, vals_compare_safe,val_is_unboxed,lit_is_unboxed in *;
  repeat match goal with
  | H : _ ∨ _ |- _ => destruct H
  | H : _ ∧ _ |- _ => destruct H
  | H : ∃ _, _ |- _ => destruct H
  | H : is_Some _ |- _ => destruct H
  end;
  simpl in *;
  first [by eauto | congruence].

Ltac source_stuck_sidecond_bt :=
  intros;
  match goal with
  | |- ¬ _ => intros ?; source_stuck_sidecond_bt
  | |- _ ∧ _ => split; source_stuck_sidecond_bt
  | |- _ ∨ _ => left; source_stuck_sidecond_bt
  | |- _ ∨ _ => right; source_stuck_sidecond_bt
  | |- _ => source_stuck_sidecond
  end.

Ltac discr_source :=
  let discr _ :=
    iIntros "%";
    repeat match goal with
           | H : _ ∧ _ |- _ => destruct H
           | H : _ ∨ _ |- _ => destruct H
           | H : ∃ _, _ |- _ => destruct H
           end; subst in
  match goal with
  | |- envs_entails _ (source_red _ _ _) => iApply source_red_safe_implies; [discr ()]
  | |- envs_entails _ (sim_expr _ _ _ _) => iApply sim_safe_implies; [discr ()]
  | |- envs_entails _ (sim _ _ _ _) => iApply sim_safe_implies; [discr ()]
  end.

(** [safe_reach_bind e] works on goals of the form [safe_reach P e' σ Φ]
    and tries to find a subexpression of e' matching e and applies the bind lemma for
    it (similar to sim_bind and friends). *)
Tactic Notation "safe_reach_bind" open_constr(efoc) :=
  lazymatch goal with
  | |- safe_reach _ ?e _ _ =>
    reshape_expr e ltac:(fun K e' =>
                           unify e' efoc;
                           eapply (safe_reach_bind _ e' _ _ K); simpl
                        )
  end.

(** [safe_reach_fill e] works on goals of the form [safe_reach P e' σ (post_in_ectx Φ)]
    and tries to find a subexpression e'' of e' matching e and results in a goal
    [safe_reach P e'' σ (post_in_ectx Φ)] (i.e. it discards the evaluation context around e''). *)
Tactic Notation "safe_reach_fill" open_constr(efoc) :=
  lazymatch goal with
  | |- safe_reach _ ?e _ _ =>
    reshape_expr e ltac:(fun K e' =>
                           unify e' efoc;
                           eapply (fill_safe_reach _ e' _ _ K)
                        )
  end.


(** Applies gen_log_rel_subst for each element of [l],
    introduces the new terms under some fresh names,
    calls [cont] on the remaining goal,
    then reverts all the fresh names. *)
Local Ltac log_rel_subst_l l cont :=
  match l with
  | nil => cont ()
  | ?x :: ?l =>
    iApply (gen_log_rel_subst _ _ x _ _ #() with "[]");
    [ done (* [val_rel] for the dummy value *)
    | let v_t := fresh "v_t" in
      let v_s := fresh "v_s" in
      let H := iFresh in
      iIntros (v_t v_s) "!#";
      let pat := constr:(intro_patterns.IIntuitionistic (intro_patterns.IIdent H)) in
      iIntros pat;
      rewrite ->!subst_map_singleton;
      log_rel_subst_l l ltac:(fun _ =>
        cont ();
        iRevert (v_t v_s) H
      )
    ]
  end.

(** Turns an [gen_log_rel] goal into a [sim] goal by applying a
    suitable substitution. *)
Ltac log_rel :=
  iStartProof;
  lazymatch goal with
  | |- proofmode.environments.envs_entails _ (gen_log_rel ?val_rel ?town ?e_t ?e_s) =>
    let h_t := get_head e_t in try unfold h_t;
    let h_s := get_head e_s in try unfold h_s
  end;
  lazymatch goal with
  | |- proofmode.environments.envs_entails _ (gen_log_rel ?val_rel ?town ?e_t ?e_s) =>
    let e_t' := W.of_expr e_t in
    let e_s' := W.of_expr e_s in
    let free := eval vm_compute in (remove_dups (W.free_vars e_t' ++ W.free_vars e_s')) in
    log_rel_subst_l free ltac:(fun _ =>
        (* FIXME: we shouldn't [simpl] the entire user goal! that can have bad side-effects. *)
        simpl; simpl_subst;
        iApply gen_log_rel_closed; [apply empty_union_L; split; solve_is_closed|])
  end.
