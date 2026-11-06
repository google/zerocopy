From iris Require Import bi.bi.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior hoare.
From simuliris.simulang.simple_inv Require Export inv.

(** * Derived rules for the simple invariant (without support for exploiting non-atomics) *)
(**
   This file proves the derived rules shown in the paper, 
   in particular the Hoare triples and quadruples for the simple logic without support for exploiting non-atomics (Section 2 of the paper).
   For the triples that hold for the extended non-atomic logic (used from Section 3 on), see file [theories/simulang/na_inv/examples/derived.v].
*)

Section derived.
  Context `{simpleGS Σ}.

  Implicit Types
    (P : iProp Σ) (Φ : expr → expr → iProp Σ) (Ψ : expr → iProp Σ)
    (e_t e_s : expr)
    (v_t v_s : val)
    (π : thread_id).

  (* Rules for the assertion [e_s ⇝ Q] ([SafeImplies]) shown in the paper. 
    In contrast to the presentation in the paper, [SafeImplies] is additionally parameterized by the program [p] and the state [σ], 
     in order to allow the predicate [Q] to make statements about both of these.
  *)
  Lemma safe_div_int_nonzero v1 v2 p σ : SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n ∧ n ≠ 0%Z))%V p (BinOp QuotOp (Val v1) (Val v2)) σ.
  Proof. apply _. Qed.

  (* for expression postconditions *)
  Lemma sim_bind' P e_t e_s K_t K_s π Φ Φ' :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ' }}}) →
    (∀ e_t' e_s', ⊢ {{{ Φ' e_t' e_s' }}} fill K_t e_t' ⪯[π] fill K_s e_s' {{{ Φ }}}) →
    ⊢ {{{ P }}} fill K_t e_t ⪯[π] fill K_s e_s {{{ Φ }}}.
  Proof.
    intros He HK. iModIntro. iIntros "HP". iPoseProof (He with "HP") as "Hs".
    iApply sim_expr_bind. iApply (sim_expr_wand with "Hs []").
    iIntros (e_t' e_s') "Hp". by iApply HK.
  Qed.

  (* for value postconditions *)
  Lemma sim_bind P e_t e_s K_t K_s π (Φ Φ' : val → val → iProp Σ) :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ lift_post Φ' }}}) →
    (∀ v_t' v_s', ⊢ {{{ Φ' v_t' v_s' }}} fill K_t v_t' ⪯[π] fill K_s v_s' {{{ lift_post Φ }}}) →
    ⊢ {{{ P }}} fill K_t e_t ⪯[π] fill K_s e_s {{{ lift_post Φ }}}.
  Proof.
    intros He HK. iModIntro. iIntros "HP". iPoseProof (He with "HP") as "Hs".
    iApply sim_bind. iApply (sim_wand with "Hs []").
    iIntros (v_t' v_s') "Hp". by iApply HK.
  Qed.

  (* for expression postconditions *)
  Lemma sim_frame' P e_t e_s π Φ R :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P ∗ R }}} e_t ⪯[π] e_s {{{ λ e_t' e_s', Φ e_t' e_s' ∗ R }}}.
  Proof.
    iIntros (Hs) "!> [HP HR]".
    iPoseProof (Hs with "HP") as "Hs".
    iApply (sim_expr_wand with "Hs [HR]"). eauto with iFrame.
  Qed.

  (* for value postconditions *)
  Lemma sim_frame P e_t e_s π (Φ : val → val → iProp Σ) R :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ lift_post Φ }}}) →
    ⊢ {{{ P ∗ R }}} e_t ⪯[π] e_s {{{ lift_post (λ v_t' v_s', Φ v_t' v_s' ∗ R) }}}.
  Proof.
    iIntros (Hs) "!> [HP HR]".
    iPoseProof (Hs with "HP") as "Hs".
    iApply (sim_wand with "Hs [HR]"). eauto with iFrame.
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

  (** ** SimuLang triples and quadruples specific to the simple invariant *)

  (** *** Source triples *)
  Lemma source_load l q v P o π :
    o = ScOrd ∨ o = Na1Ord →
    ⊢ [{{ l ↦s{#q} v }}] Load o #l @ π [{{ λ v', ⌜v' = v⌝ ∗ l ↦s{#q} v }}]s.
  Proof.
    iIntros (Ho) "!> Hpre". iApply (source_red_load with "Hpre"); first by eauto.
    iIntros "Hl". source_finish. eauto with iFrame.
  Qed.

  Lemma source_store l (v v' : val) o P π :
    o = ScOrd ∨ o = Na1Ord →
    ⊢ [{{ l ↦s v' }}] Store o #l v @ π [{{ λ v'', ⌜v'' = #()⌝ ∗ l ↦s v }}]s.
  Proof.
    iIntros (Ho) "!> Hs".
    iApply (source_red_store with "Hs"); first done. iIntros "Hs".
    source_finish. eauto with iFrame.
  Qed.

  (** In contrast to the presentation in the paper, we also obtain ownership of [†l…s Z.to_nat n],
    which gives the total size of the allocation at [l_s]. *)
  Lemma source_alloc (v : val) (n : Z) π :
    (n > 0)%Z →
    ⊢ [{{ True }}] AllocN #n v @ π [{{ λ v', ∃ l : loc, ⌜v' = #l⌝ ∗ l ↦s∗ replicate (Z.to_nat n) v ∗ †l…s Z.to_nat n }}]s.
  Proof.
    iIntros (Hn) "!>_". source_alloc l as "Hl" "Hf"; first lia. eauto with iFrame.
  Qed.

  (** In order to free memory, we need to give up all memory of the full allocation at once,
     encoded through the allocation size assertion [†l…s Z.to_nat n]. *)
  Lemma source_freeN vs (n : nat) l π :
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

  Lemma target_store l (v v' : val) P o π :
    o = ScOrd ∨ o = Na1Ord →
    ⊢ [{{ l ↦t v' }}] Store ScOrd #l v [{{ λ v'', ⌜v'' = #()⌝ ∗ l ↦t v }}]t.
  Proof.
    iIntros (Ho) "!> Hpre". iApply (target_red_store with "Hpre"); first by eauto.
    iIntros "Hl". target_finish. eauto with iFrame.
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
    (∀ π', ⊢ {{{ P }}} e_t ⪯[π'] e_s {{{ lift_post (λ vt vs, val_rel vt vs) }}}) →
    ⊢ {{{ P }}} Fork e_t ⪯[π] Fork e_s {{{ lift_post (λ _ _, True) }}}.
  Proof.
    iIntros (Hf) "!> HP". iApply (sim_fork with "[] [HP]").
    - sim_val. eauto.
    - iIntros (π'). iApply Hf. iFrame.
  Qed.

  Lemma sim_call f v_t v_s P π Φ :
    ⊢ {{{ val_rel v_t v_s }}} Call f#f v_t ⪯[π] Call f#f v_s {{{lift_post (λ v_t' v_s', val_rel v_t' v_s') }}}.
  Proof.
    iIntros "!> #Hv". iApply sim_call; [done..|]. iIntros (??) "?"; by iApply lift_post_val. 
  Qed.

  Lemma sim_load_public l_t l_s o π :
    ⊢ {{{ l_t ↔h l_s }}} Load o #l_t ⪯[π] Load o #l_s {{{ lift_post (λ v_t v_s, val_rel v_t v_s) }}}.
  Proof.
    iIntros "!> Hb". iApply (sim_bij_load with "Hb").
    iIntros (v_t v_s) "Hv". iApply sim_value. iFrame.
  Qed.

  Lemma sim_store_public l_t l_s v_t v_s o π :
    ⊢ {{{ l_t ↔h l_s ∗ val_rel v_t v_s }}} Store o #l_t v_t ⪯[π] Store o #l_s v_s {{{ lift_post (λ v_t v_s, ⌜v_t = #()⌝ ∗ ⌜v_t = #()⌝) }}}.
  Proof.
    iIntros "!> (Hb & Hv)". iApply (sim_bij_store with "Hb Hv"). by sim_val.
  Qed.

  Lemma sim_free_public l_t l_s (n : Z) π :
    ⊢ {{{ l_t ↔h l_s }}} FreeN #n #l_t ⪯[π] FreeN #n #l_s {{{ lift_post (λ v_t v_s, ⌜v_t = #()⌝ ∗ ⌜v_t = #()⌝) }}}.
  Proof.
    iIntros "!> Hb". iApply (sim_bij_free with "Hb"). by sim_val.
  Qed.

End derived.
