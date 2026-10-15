From iris Require Import bi.bi.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior hoare.
From simuliris.simulang.na_inv Require Export inv.
From simuliris.simulang.na_inv Require Import readonly_refl adequacy.

(** * Derived rules for the non-atomic logic shown in the paper. *)
(**
   This file proves the derived rules shown in the paper, in particular the Hoare triples and quadruples for the non-atomic logic.
*)

Section derived.
  Context `{naGS Σ}.

  Implicit Types
    (P : iProp Σ) (Φ : expr → expr → iProp Σ) (Ψ : expr → iProp Σ)
    (e_t e_s : expr)
    (v_t v_s : val)
    (π : thread_id).

  Lemma sim_bind P e_t e_s K_t K_s π Φ Φ' :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ' }}}) →
    (∀ e_t' e_s', ⊢ {{{ Φ' e_t' e_s' }}} fill K_t e_t' ⪯[π] fill K_s e_s' {{{ Φ }}}) →
    ⊢ {{{ P }}} fill K_t e_t ⪯[π] fill K_s e_s {{{ Φ }}}.
  Proof.
    intros He HK. iModIntro. iIntros "HP". iPoseProof (He with "HP") as "Hs".
    iApply sim_expr_bind. iApply (sim_expr_wand with "Hs []").
    iIntros (e_t' e_s') "Hp". by iApply HK.
  Qed.

  Lemma sim_frame P e_t e_s π Φ R :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P ∗ R }}} e_t ⪯[π] e_s {{{ λ e_t' e_s', Φ e_t' e_s' ∗ R }}}.
  Proof.
    iIntros (Hs) "!> [HP HR]".
    iPoseProof (Hs with "HP") as "Hs".
    iApply (sim_expr_wand with "Hs [HR]"). eauto with iFrame.
  Qed.

  Lemma sim_base P e_t e_s π Φ :
    (⊢ P -∗ Φ e_t e_s) → ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hp) "!> HP". iApply sim_expr_base. by iApply Hp.
  Qed.

  Lemma sim_mono P Q e_t e_s π Φ Φ' :
    (⊢ P -∗ Q) →
    (∀ e_t e_s, ⊢ Φ' e_t e_s -∗ Φ e_t e_s) →
    (⊢ {{{ Q }}} e_t ⪯[π] e_s {{{ Φ' }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hpre Hpost Hs) "!>P".
    iApply (sim_expr_wand with "[P] []").
    - iApply Hs. by iApply Hpre.
    - iIntros (??) "Ha". by iApply Hpost.
  Qed.

  Lemma sim_src_safe P Q e_t e_s π Φ :
    (∀ p σ, SafeImplies Q p e_s σ) →
    (⊢ {{{ P ∗ ⌜Q⌝ }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hsafe Hs) "!> P". iApply sim_safe_implies.
    iIntros "HQ". iApply Hs. iFrame.
  Qed.

  Lemma sim_paco I e_t e_s e_t' e_s' π Φ :
    PureExec True 1 e_t e_t' →
    PureExec True 1 e_s e_s' →
    (⊢ {{{ I }}} e_t' ⪯[π] e_s' {{{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ (⌜e_t'' = e_t⌝ ∗ ⌜e_s'' = e_s⌝ ∗ I)}}}) →
    ⊢ {{{ I }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hpt Hps Hs) "!> HI". iApply (sim_lift_coind_pure with "[] HI"); [ done | done | ].
    iModIntro. iIntros "HI". by iApply Hs.
  Qed.


  (** Source triples *)
  Lemma source_sim P e_t e_s π Ψ Φ :
    (⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s) →
    (∀ e_s', ⊢ {{{ Ψ e_s' }}} e_t ⪯[π] e_s' {{{ Φ }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hsrc Hs) "!> HP". to_source.
    iApply (source_red_wand with "[HP] []"). { by iApply Hsrc. }
    iIntros (e_s') "Hpre". by iApply Hs.
  Qed.

  Lemma source_base P e_s π Ψ :
    (⊢ P -∗ Ψ e_s) →
    ⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s.
  Proof.
    iIntros (Hs) "!>HP". iApply source_red_base. iModIntro. by iApply Hs.
  Qed.

  Lemma source_bind P K_s e_s π Ψ Ψ' :
    (⊢ [{{ P }}] e_s @ π [{{ Ψ' }}]s) →
    (∀ e_s', ⊢ [{{ Ψ' e_s' }}] fill K_s e_s' @ π [{{ Ψ }}]s) →
    ⊢ [{{ P }}] fill K_s e_s @ π [{{ Ψ }}]s.
  Proof.
    iIntros (He HK) "!> HP". iApply source_red_bind.
    iApply (source_red_wand with "[HP] []"). { by iApply He. }
    iIntros (e_s') "Hpre". by iApply HK.
  Qed.

  Lemma source_focus P e_t e_s K_s π Ψ Φ :
    (⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s) →
    (∀ e_s', ⊢ {{{ Ψ e_s' }}} e_t ⪯[π] fill K_s e_s' {{{ Φ }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] fill K_s e_s {{{ Φ }}}.
  Proof.
    iIntros (Hs Hsim) "!> HP". to_source.
    iApply source_red_bind. iApply (source_red_wand with "[HP] []"). { by iApply Hs. }
    iIntros (e_s') "Hpre". to_sim. by iApply Hsim.
  Qed.

  Lemma source_frame P R e_s π Ψ :
    (⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s) →
    ⊢ [{{ P ∗ R }}] e_s @ π [{{ λ e_s', Ψ e_s' ∗ R }}]s.
  Proof.
    iIntros (Hs) "!> [HP HR]". iApply (source_red_wand with "[HP] [HR]"). { by iApply Hs. }
    eauto with iFrame.
  Qed.

  Lemma source_pure P e_s e_s' n π Ψ :
    PureExec True n e_s e_s' →
    (⊢ [{{ P }}] e_s' @ π [{{ Ψ }}]s) →
    ⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s.
  Proof.
    iIntros (Hpure Hs) "!> HP". iApply source_red_lift_pure; first done.
    by iApply Hs.
  Qed.


  (** Target triples *)
  Lemma target_sim P e_t e_s π Ψ Φ :
    (⊢ [{{ P }}] e_t [{{ Ψ }}]t) →
    (∀ e_t', ⊢ {{{ Ψ e_t' }}} e_t' ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Htgt Hs) "!> HP". to_target.
    iApply (target_red_wand with "[HP] []"). { by iApply Htgt. }
    iIntros (e_t') "Hpre". by iApply Hs.
  Qed.

  Lemma target_base P e_t Ψ :
    (⊢ P -∗ Ψ e_t) →
    ⊢ [{{ P }}] e_t [{{ Ψ }}]t.
  Proof.
    iIntros (Hs) "!>HP". iApply target_red_base. iModIntro. by iApply Hs.
  Qed.

  Lemma target_bind P K_t e_t π Ψ Ψ' :
    (⊢ [{{ P }}] e_t [{{ Ψ' }}]t) →
    (∀ e_t', ⊢ [{{ Ψ' e_t' }}] fill K_t e_t' [{{ Ψ }}]t) →
    ⊢ [{{ P }}] fill K_t e_t [{{ Ψ }}]t.
  Proof.
    iIntros (He HK) "!> HP". iApply target_red_bind.
    iApply (target_red_wand with "[HP] []"). { by iApply He. }
    iIntros (e_t') "Hpre". by iApply HK.
  Qed.

  Lemma target_focus P e_t e_s K_t π Ψ Φ :
    (⊢ [{{ P }}] e_t [{{ Ψ }}]t) →
    (∀ e_t', ⊢ {{{ Ψ e_t' }}} fill K_t e_t' ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P }}} fill K_t e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Ht Hsim) "!> HP". to_target.
    iApply target_red_bind. iApply (target_red_wand with "[HP] []"). { by iApply Ht. }
    iIntros (e_t') "Hpre". to_sim. by iApply Hsim.
  Qed.

  Lemma target_frame P R e_t π Ψ :
    (⊢ [{{ P }}] e_t [{{ Ψ }}]t) →
    ⊢ [{{ P ∗ R }}] e_t [{{ λ e_t', Ψ e_t' ∗ R }}]t.
  Proof.
    iIntros (Hs) "!> [HP HR]". iApply (target_red_wand with "[HP] [HR]"). { by iApply Hs. }
    eauto with iFrame.
  Qed.

  Lemma target_pure P e_t e_t' n π Ψ :
    PureExec True n e_t e_t' →
    (⊢ [{{ P }}] e_t' [{{ Ψ }}]t) →
    ⊢ [{{ P }}] e_t [{{ Ψ }}]t.
  Proof.
    iIntros (Hpure Hs) "!> HP". iApply target_red_lift_pure; first done.
    by iApply Hs.
  Qed.

  (** ** SimuLang triples and quadruples for the non-atomic invariant *)

  (** *** Source triples *)
  Lemma source_load l q v P o π :
    o = ScOrd ∨ o = Na1Ord →
    ⊢ [{{ l ↦s{#q} v }}] Load o #l @ π [{{ λ v', ⌜v' = v⌝ ∗ l ↦s{#q} v }}]s.
  Proof.
    iIntros (Ho) "!> Hpre". iApply (source_red_load with "Hpre"); first by eauto.
    iIntros "Hl". source_finish. eauto with iFrame.
  Qed.

  Lemma source_store_sc l (v v' : val) P π :
    ⊢ [{{ l ↦s v' ∗ na_locs π ∅ }}] Store ScOrd #l v @ π [{{ λ v'', ⌜v'' = #()⌝ ∗ l ↦s v ∗ na_locs π ∅ }}]s.
  Proof.
    iIntros "!> [Hs Hna]". iApply (sim_bij_store_sc_source with "Hs Hna"). iIntros "Hna Hs".
    source_finish. eauto with iFrame.
  Qed.

  Lemma source_store_na l (v v' : val) P π :
    ⊢ [{{ l ↦s v' }}] Store Na1Ord #l v @ π [{{ λ v'', ⌜v'' = #()⌝ ∗ l ↦s v }}]s.
  Proof.
    iIntros "!> Hs". source_store. eauto with iFrame.
  Qed.

  (** In contrast to the presentation to the paper, we also obtain ownership of [†l…s Z.to_nat n],
    which gives the total size of the allocation at [l_s]. *)
  Lemma source_alloc (v : val) (n : Z) π :
    (n > 0)%Z →
    ⊢ [{{ True }}] AllocN #n v @ π [{{ λ v', ∃ l : loc, ⌜v' = #l⌝ ∗ l ↦s∗ replicate (Z.to_nat n) v ∗ †l…s Z.to_nat n }}]s.
  Proof.
    iIntros (Hn) "!>_". source_alloc l as "Hl" "Hf"; first lia. eauto with iFrame.
  Qed.

  (** In order to free memory, we need to give up all memory of the full allocation at once,
     encoded through the allocation size assertion [†l…s Z.to_nat n]. *)
  Lemma source_free vs (n : nat) l π :
    length vs = n →
    ⊢ [{{ l ↦s∗ vs ∗ †l…s Z.to_nat n  }}] FreeN #n #l @ π [{{ λ v', ⌜v' = #()⌝ }}]s.
  Proof.
    iIntros (Hn) "!> [Hs Hf]". source_free; first lia. eauto.
  Qed.

  Lemma source_call f x e (v : val) P π Ψ :
    (⊢ [{{ f @s (x, e) ∗ P }}] apply_func (x, e)%core v @ π [{{ Ψ }}]s) →
    ⊢ [{{ f @s (x, e) ∗ P }}] Call f#f v @ π [{{ Ψ }}]s.
  Proof.
    iIntros (Hs) "!> [#Hc HP]". iApply (source_red_call with "Hc").
    iApply Hs. iFrame "HP Hc".
  Qed.

  (** *** Target triples *)
  Lemma target_load l q v P o :
    o = ScOrd ∨ o = Na1Ord →
    ⊢ [{{ l ↦t{#q} v }}] Load o #l [{{ λ v', ⌜v' = v⌝ ∗ l ↦t{#q} v }}]t.
  Proof.
    iIntros (Ho) "!> Hpre". iApply (target_red_load with "Hpre"); first by eauto.
    iIntros "Hl". target_finish. eauto with iFrame.
  Qed.

  (* does NOT hold for the na invariant *)
  Lemma target_store_sc l (v v' : val) P π :
    ⊢ [{{ l ↦t v' ∗ na_locs π ∅ }}] Store ScOrd #l v [{{ λ v'', ⌜v'' = #()⌝ ∗ l ↦t v ∗ na_locs π ∅ }}]t.
  Proof.
  Abort.

  Lemma target_store_na l (v v' : val) P :
    ⊢ [{{ l ↦t v' }}] Store Na1Ord #l v [{{ λ v'', ⌜v'' = #()⌝ ∗ l ↦t v }}]t.
  Proof.
    iIntros "!> Hs". target_store. eauto with iFrame.
  Qed.

  (** In contrast to the presentation to the paper, we also obtain ownership of [†l…t Z.to_nat n],
    which gives the total size of the allocation at [l_t]. *)
  Lemma target_alloc (v : val) (n : Z) :
    (n > 0)%Z →
    ⊢ [{{ True }}] AllocN #n v [{{ λ v', ∃ l : loc, ⌜v' = #l⌝ ∗ l ↦t∗ replicate (Z.to_nat n) v ∗ †l…t Z.to_nat n }}]t.
  Proof.
    iIntros (Hn) "!>_". target_alloc l as "Hl" "Hf"; first lia. eauto with iFrame.
  Qed.

  (** In order to free memory, we need to give up all memory of the full allocation at once,
     encoded through the allocation size assertion [†l…t Z.to_nat n]. *)
  Lemma target_free vs (n : nat) l :
    length vs = n →
    ⊢ [{{ l ↦t∗ vs ∗ †l…t Z.to_nat n  }}] FreeN #n #l [{{ λ v', ⌜v' = #()⌝ }}]t.
  Proof.
    iIntros (Hn) "!> [Hs Hf]". target_free; first lia. eauto.
  Qed.

  Lemma target_call f x e (v : val) P Ψ :
    (⊢ [{{ f @t (x, e) ∗ P }}] apply_func (x, e)%core v [{{ Ψ }}]t) →
    ⊢ [{{ f @t (x, e) ∗ P }}] Call f#f v [{{ Ψ }}]t.
  Proof.
    iIntros (Hs) "!> [#Hc HP]". iApply (target_red_call with "Hc").
    iApply Hs. iFrame "HP Hc".
  Qed.

  (** *** Quadruples *)
  Lemma sim_while I c_t c_s b_t b_s π Φ :
    let w_t := (while: c_t do b_t od)%E in
    let w_s := (while: c_s do b_s od)%E in
    (⊢ {{{ I }}} if: c_t then b_t;; w_t else #() ⪯[π] if: c_s then b_s;; w_s else #()
        {{{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ (⌜e_t'' = w_t⌝ ∗ ⌜e_s'' = w_s⌝ ∗ I)}}}) →
    ⊢ {{{ I }}} w_t ⪯[π] w_s {{{ Φ }}}.
  Proof.
    intros w_t w_s Hs. iApply sim_paco; [ apply pure_while.. | apply Hs].
  Qed.

  Lemma sim_while_simple I c_t c_s b_t b_s π Q Φ :
    (⊢ {{{ I }}} c_t ⪯[π] c_s {{{ lift_post (λ v_t v_s,
          val_rel v_t v_s ∗ ((⌜v_s = #true⌝ ∗ I) ∨ ( ⌜v_s ≠ #true⌝ ∗ Q)))}}}) →
    (⊢ {{{ I }}} b_t ⪯[π] b_s {{{ lift_post (λ _ _, I) }}}) →
    ⊢ {{{ I }}} while: c_t do b_t od ⪯[π] while: c_s do b_s od {{{ lift_post (λ _ _, Q) }}}.
  Proof.
    iIntros (Hc Hb). iApply sim_while. iIntros "!>HI".
    sim_bind c_t c_s. iApply (sim_wand with "[HI] []"). { by iApply Hc. }
    iIntros (v_t v_s) "Hc".
    iApply sim_safe_implies. iIntros "(%b & ->)".
    iDestruct "Hc" as "(Hv & [(% & HI) | (% & HQ)])".
    - simplify_eq. val_discr_source "Hv". sim_pures.
      sim_bind b_t b_s. iApply (sim_wand with "[HI] []"). { by iApply Hb. }
      iIntros (? ?) "HI". sim_pures. iApply sim_expr_base. eauto with iFrame.
    - val_discr_source "Hv". destruct b; first done.
      sim_pures. iApply sim_expr_base. iLeft. iApply lift_post_val. done.
  Qed.

  Lemma sim_global_var (A : string) π :
    ⊢ {{{ True }}} GlobalVar A ⪯[π] GlobalVar A {{{ lift_post (λ v_t v_s, ∃ l_t l_s : loc, ⌜v_t = #l_t⌝ ∗ ⌜v_s = #l_s⌝ ∗ l_t ↔h l_s) }}}.
  Proof.
    iIntros "!> _". iApply (globalbij.sim_global_var loc_rel). { exact sim_bij_contains_globalbij. }
    iIntros (??) "Hb". iApply lift_post_val. eauto with iFrame.
  Qed.

  (** To insert into the bijection, we also need to give up the allocation size control
     for both allocations -- crucially, we again need to make the full allocation public at once,
     and the allocations need to have the same size in source and target. *)
  Lemma sim_insert_bijN l_t l_s vs_t vs_s n e_t e_s π Φ P :
    n > 0 →
    length vs_t = n →
    length vs_s = n →
    (⊢ {{{ l_t ↔h l_s ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ l_t ↦t∗ vs_t ∗ l_s ↦s∗ vs_s ∗ ([∗ list] v_t; v_s ∈ vs_t; vs_s, val_rel v_t v_s) ∗ †l_s…s n ∗ †l_t…t n ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hn Hlen_t Hlen_s Hs) "!> (Ht & Hs & Hv & Hf_s & Hf_t & HP)".
    iApply (sim_bij_insertN with "Hf_t Hf_s Ht Hs Hv"); [lia | lia | lia | ].
    iIntros "Hl". iApply Hs. iFrame.
  Qed.

  Lemma sim_insert_bij l_t l_s v_t v_s e_t e_s π Φ P :
    (⊢ {{{ l_t ↔h l_s ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ l_t ↦t v_t ∗ l_s ↦s v_s ∗ val_rel v_t v_s ∗ †l_s…s 1 ∗ †l_t…t 1 ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hs) "!> (Ht & Hs & Hv & Hf_s & Hf_t & HP)".
    iApply (sim_bij_insert with "Hf_t Hf_s Ht Hs Hv").
    iIntros "Hl". iApply Hs. iFrame.
  Qed.

  Lemma sim_fork e_t e_s P π Φ :
    (∀ π', ⊢ {{{ P ∗ na_locs π' ∅ }}} e_t ⪯[π'] e_s {{{ lift_post (λ vt vs, na_locs π' ∅ ∗ val_rel vt vs) }}}) →
    ⊢ {{{ P ∗ na_locs π ∅ }}} Fork e_t ⪯[π] Fork e_s {{{ lift_post (λ _ _, na_locs π ∅) }}}.
  Proof.
    iIntros (Hf) "!> [HP Hna]". iApply (sim_bij_fork with "Hna [] [HP]").
    - iIntros "Hna". sim_val. eauto.
    - iIntros (π') "Hna". iApply Hf. iFrame.
  Qed.

  Lemma sim_call f v_t v_s P π Φ :
    ⊢ {{{ val_rel v_t v_s ∗ na_locs π ∅ }}} Call f#f v_t ⪯[π] Call f#f v_s {{{lift_post (λ v_t' v_s', val_rel v_t' v_s' ∗ na_locs π ∅) }}}.
  Proof.
    iIntros "!> [#Hv Hna]". iApply (sim_call with "[Hna]"); [ done.. | by iFrame| ].
    iIntros (??) "[Hna Hv']". iApply lift_post_val. iFrame.
  Qed.

  Lemma sim_load_sc_public l_t l_s C π :
    C !! l_s = None →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π C }}} Load ScOrd #l_t ⪯[π] Load ScOrd #l_s {{{ lift_post (λ v_t v_s, val_rel v_t v_s ∗ na_locs π C) }}}.
  Proof.
    iIntros (Hl) "!> [Hb Hna]". iApply (sim_bij_load with "Hb Hna"); [done | done | ].
    iIntros (v_t v_s) "Hv Hna". iApply sim_value. iFrame.
  Qed.

  Lemma sim_load_na_public l_t l_s C π :
    C !! l_s = None →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π C }}} Load Na1Ord #l_t ⪯[π] Load Na1Ord #l_s {{{ lift_post (λ v_t v_s, val_rel v_t v_s ∗ na_locs π C) }}}.
  Proof.
    iIntros (Hl) "!> [Hb Hna]". iApply (sim_bij_load with "Hb Hna"); [done | done | ].
    iIntros (v_t v_s) "Hv Hna". iApply sim_value. iFrame.
  Qed.

  (** This requires there to be no exploited locations for this thread.
     We can also prove something stronger (see [sim_bij_store_sc]): we can "refresh" all exploited locations for which exploitable operations are reachable after the store.
  *)
  Lemma sim_store_sc_public l_t l_s v_t v_s π :
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π ∅ ∗ val_rel v_t v_s }}} Store ScOrd #l_t v_t ⪯[π] Store ScOrd #l_s v_s {{{ lift_post (λ v_t v_s, ⌜v_t = #()⌝ ∗ ⌜v_t = #()⌝ ∗ na_locs π ∅) }}}.
  Proof.
    iIntros "!> (Hb & Hna & Hv)". iApply (sim_bij_store_sc empty_ectx empty_ectx with "Hb Hna Hv"); [done | | ].
    { intros ?????. rewrite lookup_empty. congruence. }
    iIntros "Hna". iApply sim_value. eauto with iFrame.
  Qed.

  Lemma sim_store_na_public l_t l_s v_t v_s C π :
    C !! l_s = None →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π C ∗ val_rel v_t v_s }}} Store Na1Ord #l_t v_t ⪯[π] Store Na1Ord #l_s v_s {{{ lift_post (λ v_t v_s, ⌜v_t = #()⌝ ∗ ⌜v_t = #()⌝ ∗ na_locs π C) }}}.
  Proof.
    iIntros (Hc) "!> (Hb & Hna & Hv)". iApply (sim_bij_store_na with "Hb Hna Hv"); [done | ].
    iIntros "Hna". iApply sim_value. eauto with iFrame.
  Qed.

  Lemma sim_freeN_public l_t l_s C n π :
    (∀ i : Z, (0 ≤ i < n)%Z → C !! (l_s +ₗ i) = None) →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π C }}} FreeN #n #l_t ⪯[π] FreeN #n #l_s {{{ lift_post (λ v_t v_s, ⌜v_t = #()⌝ ∗ ⌜v_t = #()⌝ ∗ na_locs π C) }}}.
  Proof.
    iIntros (Hc) "!> (Hb & Hna)". iApply (sim_bij_free with "Hb Hna"); [done | ].
    iIntros "Hna". iApply sim_value. eauto with iFrame.
  Qed.

  Lemma sim_free_public l_t l_s C π :
    C !! l_s = None →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π C }}} Free #l_t ⪯[π] Free #l_s {{{ lift_post (λ v_t v_s, ⌜v_t = #()⌝ ∗ ⌜v_t = #()⌝ ∗ na_locs π C) }}}.
  Proof.
    intros Hc. apply sim_freeN_public. intros i Hi. assert (i = 0) as -> by lia.
    replace (Z.of_nat O) with 0%Z by lia. rewrite loc_add_0. done.
  Qed.


  (** Exploitation triples *)
  Lemma sim_exploit_store P π (l_t l_s : loc) Φ e_s e_t col :
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' σ', ∃ v' : val, e' = Store Na1Ord #l_s v' ∧ ∃ v, σ_s.(heap) !! l_s = Some (RSt 0, v)))) →
    col !! l_s = None →
    (∀ v_t v_s, ⊢ {{{ l_t ↦t v_t ∗ l_s ↦s v_s ∗ val_rel v_t v_s ∗ na_locs π (<[l_s := (l_t, NaExcl)]>col) ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π col ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hreach Hcol Hs) "!> (Hbij & Hna & HP)".
    iApply (sim_bij_exploit_store with "Hbij Hna"); [done | done | ].
    iIntros (??) "Ht Hs Hv Hna". iApply Hs. iFrame.
  Qed.

  Lemma sim_exploit_load P π (l_t l_s : loc) Φ e_s e_t col :
    (∀ P_s σ_s, safe_reach P_s e_s σ_s (post_in_ectx (λ e' σ', e' = (Load Na1Ord #l_s) ∧ ∃ n v, σ_s.(heap) !! l_s = Some (RSt n, v)))) →
    col !! l_s = None →
    (∀ q v_t v_s, ⊢ {{{ l_t ↦t{#q} v_t ∗ l_s ↦s{#q} v_s ∗ val_rel v_t v_s ∗ na_locs π (<[l_s := (l_t, NaRead q)]>col) ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π col ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hreach Hcol Hs) "!> (Hbij & Hna & HP)".
    iApply (sim_bij_exploit_load with "Hbij Hna"); [done | done | ].
    iIntros (???) "Ht Hs Hv Hna". iApply Hs. iFrame.
  Qed.

  Lemma sim_exploit_release ns π Φ e_s e_t col l_s l_t v_t v_s P :
    let q := if ns is NaRead q then q else 1%Qp in
    col !! l_s = Some (l_t, ns) →
    (⊢ {{{ na_locs π (delete l_s col) ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ l_t ↔h l_s ∗ na_locs π col ∗ l_t ↦t{#q} v_t ∗ l_s ↦s{#q} v_s ∗ val_rel v_t v_s ∗ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    intros q. iIntros (Hcol Hs) "!> (Hbij & Hna & Ht & Hs & Hv & HP)".
    iApply (sim_bij_release with "Hbij Hna Ht Hs Hv"); first done.
    iIntros "Hna". iApply Hs. iFrame.
  Qed.

End derived.
