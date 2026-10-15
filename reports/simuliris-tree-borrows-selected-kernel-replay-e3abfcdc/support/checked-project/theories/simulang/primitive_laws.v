(** * State interpretation for SimpLang

This file provides a state interpretation of SimpLang. This state
interpretation provides points-to predicates for source and target and
assertions for functions. Additionally, the state interpretation can
be extended via a custom invariant [sheapInv]. This file also proves
the basic laws of the program logic, assuming that [sheapInv] allows
them. *)

From iris.proofmode Require Export proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.simulang Require Export class_instances tactics notation logical_heap.

Class sheapGS (Σ: gFunctors) := SHeapGS {
  (* These instances need to have a lower priority than the sheapGpreS
  instances as otherwise the statement of [simplang_adequacy] uses the
  wrong instance. *)
  sheapG_gen_progG :: gen_sim_progGS string func func Σ | 1;
  sheapG_heapG :: heapG Σ | 1;
  sheapG_heap_target : heap_names;
  sheapG_heap_source : heap_names;
}.
Class sheapGpreS (Σ: gFunctors) := SHeapGpreS {
  sbij_pre_heapG :: heapG Σ | 10;
  sbij_pre_progG :: gen_progGpreS Σ string func | 10;
}.
Definition sheapΣ := #[heapΣ; gen_progΣ string func].
Global Instance subG_sheapΣ Σ :
  subG sheapΣ Σ → sheapGpreS Σ.
Proof. solve_inG. Qed.

(** [sheapInv] allows extending the state interpretation with
   additional components, i.e., invariants on the relation of source
   and target programs and states. *)
Class sheapInv (Σ : gFunctors) := SHeapRel {
  (** [sheap_inv P_s σ_s T_s] is parametrized by the source program
  [P_s], source state [σ_s] and source thread pool [T_s]. *)
  sheap_inv : prog → state → list expr → iProp Σ;
  sheap_inv_pure_prim_step P_s σ_s e_s T π e_s':
    T !! π = Some e_s →
    (∀ σ_s', σ_s'.(globals) = σ_s.(globals) → prim_step P_s e_s σ_s' e_s' σ_s' []) →
    sheap_inv P_s σ_s T ⊢
    sheap_inv P_s σ_s (<[π:=e_s']>T);
  sheap_ext_rel : thread_id → val → val → iProp Σ;
}.
(** Since [sheap_inv] is parametrized by the state of the source
  program, operations that change the source state don't necessarily
  preserve [sheap_inv]. Thus, each operation that changes the source
  state has a type class [sheapInvSupports...] type class which one
  can implement for a specific [sheapInv]. The lemmas for the source
  operations below have these typeclasses as precondition. If
  [sheap_inv] does not actually depend on the source state, one can
  also implement [sheapInvStateIndependent] to automatically get
  instances of all [sheapInvSupports...] typeclasses. *)
Class sheapInvSupportsLoad `{!sheapInv Σ} (o : order) := {
  sheap_inv_load P_s σ_s T_s (l_s : loc) (v : val) n K_s π:
    T_s !! π = Some (fill K_s (Load o #l_s)) →
    heap σ_s !! l_s = Some (RSt n, v) →
    o ≠ Na2Ord →
    pool_safe P_s T_s σ_s →
    heap_wf σ_s →
    sheap_inv P_s σ_s T_s ⊢
    sheap_inv P_s σ_s (<[π := fill K_s v]>T_s);
}.
Class sheapInvSupportsStore `{!sheapInv Σ} (o : order) := {
  sheap_inv_store P_s σ_s T_s (l_s : loc) (v v': val) K_s π:
    heap σ_s !! l_s = Some (RSt 0, v) →
    T_s !! π = Some (fill K_s (Store o #l_s v')) →
    pool_safe P_s T_s σ_s →
    heap_wf σ_s →
    sheap_inv P_s σ_s T_s ⊢
    sheap_inv P_s (state_upd_heap <[l_s:=(RSt 0, v')]> σ_s) (<[π := fill K_s #()]>T_s);
}.
Class sheapInvSupportsAlloc `{!sheapInv Σ} := {
  sheap_inv_alloc P_s σ_s T_s (n : Z) (v : val) K_s π:
    (0 < n)%Z →
    T_s !! π = Some (fill K_s (AllocN #n v)) →
    pool_safe P_s T_s σ_s →
    heap_wf σ_s →
    sheap_inv P_s σ_s T_s ⊢
    sheap_inv P_s
         {| heap :=
             heap_array (dyn_loc (fresh (used_dyn_blocks σ_s)))
               (replicate (Z.to_nat n) v) ∪ heap σ_s;
           used_dyn_blocks := {[fresh (used_dyn_blocks σ_s)]} ∪ used_dyn_blocks σ_s;
           globals := globals σ_s
         |} (<[π:=fill K_s #(dyn_loc (fresh (used_dyn_blocks σ_s)))]> T_s);
}.
Class sheapInvSupportsFree `{!sheapInv Σ} := {
  sheap_inv_free P_s σ_s T_s (n : Z) (l : loc) K_s π:
    (0 < n)%Z →
    T_s !! π = Some (fill K_s (FreeN #n #l)) →
    pool_safe P_s T_s σ_s →
    heap_wf σ_s →
    sheap_inv P_s σ_s T_s ⊢
    sheap_inv P_s (state_upd_heap (free_mem l (Z.to_nat n)) σ_s) (<[π:=fill K_s #()]> T_s);
}.
Class sheapInvSupportsFork `{!sheapInv Σ} := {
  sheap_inv_fork P_s σ_s T_s K_s π e_s:
    T_s !! π = Some (fill K_s (Fork e_s)) →
    pool_safe P_s T_s σ_s →
    heap_wf σ_s →
    sheap_inv P_s σ_s T_s ⊢
    sheap_inv P_s σ_s (<[π:=fill K_s #()]> T_s ++ [e_s])
}.
Class sheapInvStateIndependent `{!sheapInv Σ} := {
  sheap_inv_state_independent P_s1 σ_s1 T1 P_s2 σ_s2 T2:
    sheap_inv P_s1 σ_s1 T1 ⊢ sheap_inv P_s2 σ_s2 T2
}.
Global Instance sheap_inv_state_independent_supports_load `{!sheapInv Σ} `{!sheapInvStateIndependent} o:
  sheapInvSupportsLoad o.
Proof. constructor => *. apply: sheap_inv_state_independent. Qed.
Global Instance sheap_inv_state_independent_supports_store `{!sheapInv Σ} `{!sheapInvStateIndependent} o:
  sheapInvSupportsStore o.
Proof. constructor => *. apply: sheap_inv_state_independent. Qed.
Global Instance sheap_inv_state_independent_supports_alloc `{!sheapInv Σ} `{!sheapInvStateIndependent}:
  sheapInvSupportsAlloc.
Proof. constructor => *. apply: sheap_inv_state_independent. Qed.
Global Instance sheap_inv_state_independent_supports_free `{!sheapInv Σ} `{!sheapInvStateIndependent}:
  sheapInvSupportsFree.
Proof. constructor => *. apply: sheap_inv_state_independent. Qed.
Global Instance sheap_inv_state_independent_supports_fork `{!sheapInv Σ} `{!sheapInvStateIndependent}:
  sheapInvSupportsFork.
Proof. constructor => *. apply: sheap_inv_state_independent. Qed.


Global Program Instance sheapGS_simulirisGS `{!sheapGS Σ} `{!sheapInv Σ} : simulirisGS (iPropI Σ) simp_lang := {
  state_interp P_t σ_t P_s σ_s T_s :=
    (has_prog (hG := gen_prog_inG_target) P_t ∗
     has_prog (hG := gen_prog_inG_source) P_s ∗
     heap_ctx sheapG_heap_target σ_t ∗
     heap_ctx sheapG_heap_source σ_s ∗
     sheap_inv P_s σ_s T_s
    )%I;
  ext_rel := sheap_ext_rel;
}.
Next Obligation.
  iIntros (?????????????) "($&$&$&$&?)".
  by iApply sheap_inv_pure_prim_step.
Qed.

(* TODO: add dfrac notions back if the heap supports them*)
Notation "l '↦t[' st ']{#' q } v" := (heap_pointsto sheapG_heap_target l st q v%V)
  (at level 20, format "l  ↦t[ st ]{# q }  v") : bi_scope.
Notation "l '↦t[' st ] v" := (heap_pointsto sheapG_heap_target l st 1 v%V)
  (at level 20, format "l  ↦t[ st ]  v") : bi_scope.
Notation "l '↦t{#' q } v" := (heap_pointsto sheapG_heap_target l (RSt 0) q v%V)
  (at level 20, format "l  ↦t{# q }  v") : bi_scope.
Notation "l '↦t' v" := (heap_pointsto sheapG_heap_target l (RSt 0) 1 v%V)
  (at level 20, format "l  ↦t  v") : bi_scope.
Notation "l '↦s[' st ']{#' q } v" := (heap_pointsto sheapG_heap_source l st q v%V)
  (at level 20, format "l  ↦s[ st ]{# q }  v") : bi_scope.
Notation "l '↦s[' st ] v" := (heap_pointsto sheapG_heap_source l st 1 v%V)
  (at level 20, format "l  ↦s[ st ]  v") : bi_scope.
Notation "l '↦s{#' q } v" := (heap_pointsto sheapG_heap_source l (RSt 0) q v%V)
  (at level 20, format "l  ↦s{# q }  v") : bi_scope.
Notation "l '↦s' v" := (heap_pointsto sheapG_heap_source l (RSt 0) 1 v%V)
  (at level 20, format "l  ↦s  v") : bi_scope.

Notation "l ↦t∗[ st ]{# q } vs" := (heap_pointsto_vec_st sheapG_heap_target l st q vs)
  (at level 20, format "l  ↦t∗[ st ]{# q }  vs") : bi_scope.
Notation "l ↦t∗[ st ] vs" := (heap_pointsto_vec_st sheapG_heap_target l st 1 vs)
  (at level 20, format "l  ↦t∗[ st ]  vs") : bi_scope.
Notation "l ↦t∗{# q } vs" := (heap_pointsto_vec sheapG_heap_target l q vs)
  (at level 20, format "l  ↦t∗{# q }  vs") : bi_scope.
Notation "l ↦t∗ vs" := (heap_pointsto_vec sheapG_heap_target l 1 vs)
  (at level 20, format "l  ↦t∗  vs") : bi_scope.
Notation "l ↦s∗[ st ]{# q } vs" := (heap_pointsto_vec_st sheapG_heap_source l st q vs)
  (at level 20, format "l  ↦s∗[ st ]{# q }  vs") : bi_scope.
Notation "l ↦s∗[ st ] vs" := (heap_pointsto_vec_st sheapG_heap_source l st 1 vs)
  (at level 20, format "l  ↦s∗[ st ]  vs") : bi_scope.
Notation "l ↦s∗{# q } vs" := (heap_pointsto_vec sheapG_heap_source l q vs)
  (at level 20, format "l  ↦s∗{# q }  vs") : bi_scope.
Notation "l ↦s∗ vs" := (heap_pointsto_vec sheapG_heap_source l 1 vs)
  (at level 20, format "l  ↦s∗  vs") : bi_scope.

(** Program assertions *)
Notation "f '@t' fn" := (has_fun (hG:=gen_prog_inG_target) f fn)
  (at level 20, format "f  @t  fn") : bi_scope.
Notation "f '@s' fn" := (has_fun (hG:=gen_prog_inG_source) f fn)
  (at level 20, format "f  @s  fn") : bi_scope.

(** Allocation size notation *)
Notation target_block_size l := (heap_block_size sheapG_heap_target l 1).
Notation source_block_size l := (heap_block_size sheapG_heap_source l 1).

Notation "† l '…?t' n" := (heap_freeable sheapG_heap_target l 1 n)
  (at level 20, format "† l …?t  n") : bi_scope.
Notation "† l '…t' n" := (heap_freeable sheapG_heap_target l 1 (Some n))
  (at level 20, format "† l …t  n") : bi_scope.
(* Level 0 does not work, presumably because of the shared prefix with the other level-20 notations? *)
(* (see https://github.com/rocq-prover/rocq/issues/22215) *)
#[warnings="-closed-notation-not-level-0"]
Notation "† l '…t' -" := (heap_freeable sheapG_heap_target l 1 None)
  (at level 20, format "† l …t  -") : bi_scope.
Notation "† l '…?s' n" := (heap_freeable sheapG_heap_source l 1 n)
  (at level 20, format "† l …?s  n") : bi_scope.
Notation "† l '…s' n" := (heap_freeable sheapG_heap_source l 1 (Some n))
  (at level 20, format "† l …s  n") : bi_scope.
#[warnings="-closed-notation-not-level-0"]
Notation "† l '…s' -" := (heap_freeable sheapG_heap_source l 1 None)
  (at level 20, format "† l …s  -") : bi_scope.

(** Global variables
    [..._globals gs] asserts that the set of global variables in target resp. source  is [gs].
    [..._global gs] asserts that [g] is a valid global variable in for the target resp. source.
 *)
(* TODO: Are there better notations? *)
Notation target_globals := (heap_globals sheapG_heap_target).
Notation target_global := (heap_global sheapG_heap_target).
Notation source_globals := (heap_globals sheapG_heap_source).
Notation source_global := (heap_global sheapG_heap_source).

Lemma sheap_init `{!sheapGpreS Σ} P_t gs_t P_s gs_s T_s :
  ⊢@{iPropI Σ} |==> ∃ `(!sheapGS Σ), ∀ `(!sheapInv Σ),
    (sheap_inv P_s (state_init gs_s) T_s -∗
      state_interp P_t (state_init gs_t) P_s (state_init gs_s) T_s) ∗
    ([∗ map] f ↦ fn ∈ P_t, f @t fn) ∗
    ([∗ map] n ↦ v ∈ gs_t, global_loc n ↦t v ∗ target_block_size (global_loc n) (Some 1)) ∗
    ([∗ map] f ↦ fn ∈ P_s, f @s fn) ∗
    ([∗ map] n ↦ v ∈ gs_s, global_loc n ↦s v ∗ source_block_size (global_loc n) (Some 1)) ∗
    source_globals (dom gs_s) ∗ target_globals (dom gs_t) ∗
    progs_are P_t P_s.
Proof.
  iMod (heap_init gs_t) as (γheap_tgt) "(Hheap_t & #Hgs_t & Hptsto_t)".
  iMod (heap_init gs_s) as (γheap_src) "(Hheap_s & #Hgs_s & Hptsto_s)".
  iMod (gen_sim_prog_init P_t P_s) as (?) "[#Hprog_t #Hprog_s]".
  iExists (SHeapGS _ _ _ γheap_tgt γheap_src). iIntros "!> %".
  iFrame. iSplitL; last iSplit; last iSplit.
  - iIntros "?". rewrite /state_interp /=. iFrame "∗#".
  - by iApply has_prog_all_funs.
  - by iApply has_prog_all_funs.
  - iFrame "Hgs_t Hgs_s".
    rewrite /progs_are /=. iIntros "!#" (P_t' P_s' σ_t' σ_s' T_s') "(#Hprog_t2 & #Hprog_s2 & _)".
    iDestruct (has_prog_agree with "Hprog_t Hprog_t2") as %->.
    iDestruct (has_prog_agree with "Hprog_s Hprog_s2") as %->.
    done.
Qed.

Section lifting.
Context `{!sheapGS Σ} `{!sheapInv Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → val → iProp Σ.
Implicit Types σ σ_s σ_t : state.
Implicit Types v v_s v_t : val.
Implicit Types l : loc.
Implicit Types f : fname.
Implicit Types π : thread_id.

(** Program for target *)
Lemma has_fun_target_agree f fn_t1 fn_t2 : f @t fn_t1 -∗ f @t fn_t2 -∗ ⌜fn_t1 = fn_t2⌝.
Proof. apply has_fun_agree. Qed.

(** Program for source *)
Lemma has_fun_source_agree f fn_s1 fn_s2 : f @s fn_s1 -∗ f @s fn_s2 -∗ ⌜fn_s1 = fn_s2⌝.
Proof. apply has_fun_agree. Qed.


(** operational lemmas for global variables *)
Lemma target_red_global n Ψ :
  target_global n -∗
  target_red #(global_loc n) Ψ -∗
  target_red (GlobalVar n) Ψ.
Proof.
  iIntros "Hg Hred". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & ?) !>".
  iDestruct (heap_global_in_ctx with "Hσ_t Hg") as %?.
  iSplitR; first by eauto with base_step.
  iIntros (e_t' efs σ_t') "%"; inv_base_step.
  iModIntro. by iFrame.
Qed.

Lemma source_red_global n Ψ π :
  (source_global n -∗ source_red #(global_loc n) π Ψ) -∗
  source_red (GlobalVar n) π Ψ.
Proof.
  iIntros "Hred". iApply source_red_lift_base_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & ?) [%Hlook %Hsafe]] !>".
  specialize (pool_safe_implies Hsafe Hlook) as ?.
  iDestruct (heap_global_intro_ctx with "Hσ_s") as "#Hg"; [done|].
  iExists _, _. iSplit. { simpl. eauto with base_step. }
  iModIntro. iDestruct ("Hred" with "[//]") as "$". iFrame.
  iApply sheap_inv_pure_prim_step; [done| |done] => ??.
  apply: fill_prim_step. apply: base_prim_step. econstructor. set_solver.
Qed.

(** operational heap lemmas *)

Lemma target_red_allocN n v Ψ:
  (0 < n)%Z →
  (∀ l, l ↦t∗ (replicate (Z.to_nat n) v) -∗
    † l …t (Z.to_nat n) -∗ target_red (of_val #l) Ψ) -∗
  target_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply target_red_lift_base_step.
  iIntros (P_t σ_t P_s σ_s T_s) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)". iModIntro.
  iDestruct (heap_ctx_wf with "Hσ_t") as %?.
  iSplitR. { eauto using alloc_fresh with base_step. }
  iIntros (e_t' efs_t σ_t') "%"; inv_base_step.
  iMod (heap_alloc with "Hσ_t") as "($&Hn&Hm)"; [done..|].
  iModIntro. iFrame. iSplitR; first done.
  by iApply ("Hloc" with "Hm [$Hn]").
Qed.

Lemma source_red_allocN π n v Ψ `{!sheapInvSupportsAlloc}:
  (0 < n)%Z →
  (∀ l, l ↦s∗ (replicate (Z.to_nat n) v) -∗
  † l …s Z.to_nat n -∗ source_red (of_val #l) π Ψ) -∗
  source_red (AllocN (Val $ LitV $ LitInt $ n) (Val v)) π Ψ.
Proof.
  iIntros (Hn) "Hloc". iApply source_red_lift_base_step.
  iIntros (P_t σ_t P_s σ_s T_s K_s) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]]".
  iDestruct (heap_ctx_wf with "Hσ_s") as %Hwf.
  iExists _, _. iSplitR. { simpl. eauto using alloc_fresh with lia base_step. }
  simpl.
  iMod (heap_alloc _ _ (fresh (used_dyn_blocks σ_s)) with "Hσ_s") as "($&Hn&Hm)"; [done| | |].
  { apply is_fresh. }
  { move => ?. apply eq_None_not_Some => -[? /Hwf]. apply is_fresh. }
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_alloc. }
  by iApply ("Hloc" with "Hm [$Hn]").
Qed.

Lemma target_red_alloc v Ψ:
  (∀ l, l ↦t v -∗ † l …t 1 -∗ target_red (of_val #l) Ψ) -∗
  target_red (Alloc (Val v)) Ψ.
Proof.
  iIntros "Ht". iApply (target_red_allocN); first lia.
  have ->: (Z.to_nat 1 = 1) by lia. simpl.
  iIntros (l). rewrite heap_pointsto_vec_singleton. iApply "Ht".
Qed.

Lemma source_red_alloc π v Ψ `{!sheapInvSupportsAlloc} :
  (∀ l, l ↦s v -∗ † l …s 1 -∗ source_red (of_val #l) π Ψ) -∗
  source_red (Alloc (Val v)) π Ψ.
Proof.
  iIntros "Ht". iApply (source_red_allocN); first lia.
  have ->: (Z.to_nat 1 = 1) by lia. simpl.
  iIntros (l). rewrite heap_pointsto_vec_singleton. iApply "Ht".
Qed.

Lemma target_red_freeN vs l (n : Z) Ψ :
  n = length vs →
  l ↦t∗ vs -∗
  † l …t Z.to_nat n -∗
  († l …t - -∗ target_red (of_val #()) Ψ) -∗
  target_red (FreeN (Val $ LitV $ LitInt n) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros (->) "Hl [% Hn] Hsim". iApply target_red_lift_base_step. rewrite Nat2Z.id.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  rewrite heap_pointsto_vec_to_st.
  iMod (heap_free with "Hσ_t Hl Hn") as (??) "[? ?]"; [ done..| ].
  iSplitR; first by eauto with lia base_step.
  iIntros "!>" (e_t' efs σ_t') "%"; inv_base_step.
  iModIntro. iFrame. iSplitR; first done.
  iApply "Hsim". by iFrame.
Qed.

Lemma target_red_free v l Ψ :
  l ↦t v -∗
  † l …t 1 -∗
  († l …t - -∗ target_red (of_val #()) Ψ) -∗
  target_red (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV (LitLoc l))) Ψ.
Proof.
  iIntros "Hl Hn". replace (1) with (Z.to_nat 1) by lia.
  iApply (target_red_freeN [v] with "[Hl] [Hn]"); [ done..| |done].
  by rewrite heap_pointsto_vec_singleton.
Qed.

Lemma source_red_freeN vs π l (n : Z) Ψ `{!sheapInvSupportsFree} :
  n = length vs →
  l ↦s∗ vs -∗
  † l …s (Z.to_nat n) -∗
  († l …s - -∗ source_red (of_val #()) π Ψ) -∗
  source_red (FreeN (Val $ LitV $ LitInt n) (Val $ LitV (LitLoc l))) π Ψ.
Proof.
  iIntros (->) "Hl [% Hn] Hsim". iApply source_red_lift_base_step. rewrite Nat2Z.id.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]]".
  iDestruct (heap_ctx_wf with "Hσ_s") as %?.
  rewrite heap_pointsto_vec_to_st.
  iMod (heap_free with "Hσ_s Hl Hn") as (??) "[? ?]"; [ done.. | ].
  iExists (Val #()), (state_upd_heap (free_mem l _) _).
  iSplitR. { iPureIntro. econstructor; eauto with lia. }
  iModIntro. iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_free. }
  iApply "Hsim". by iFrame.
Qed.

Lemma source_red_free π v l Ψ `{!sheapInvSupportsFree} :
  l ↦s v -∗
  † l …s 1 -∗
  († l …s - -∗ source_red (of_val #()) π Ψ) -∗
  source_red (FreeN (Val $ LitV $ LitInt 1) (Val $ LitV (LitLoc l))) π Ψ.
Proof.
  iIntros "Hl Hn". replace (1) with (Z.to_nat 1) by lia.
  iApply (source_red_freeN [v] with "[Hl] Hn"); [ done.. |].
  by rewrite heap_pointsto_vec_singleton.
Qed.

Lemma target_red_load_sc l q v Ψ :
  l ↦t{#q} v -∗
  (l ↦t{#q} v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load ScOrd (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iDestruct (heap_read with "Hσ_t Hl") as %[??]. iModIntro.
  iSplit; first by eauto with base_step.
  iIntros (??? Hstep); inv_base_step.
  iModIntro. iFrame. iSplit;[done|]. by iApply "Ht".
Qed.

Lemma target_red_load_na l q v Ψ :
  l ↦t{#q} v -∗
  (l ↦t{#q} v -∗ target_red (of_val v) Ψ) -∗
  target_red (Load Na1Ord (Val $ LitV $ LitLoc l)) Ψ.
Proof.
  iIntros "Hl Ht". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod (heap_read_na with "Hσ_t Hl") as (n ?) "[Hσ_t Hcont]". iModIntro.
  iSplit; first by eauto with base_step.
  iIntros (??? Hstep) "!>"; inv_base_step.
  iFrame. iSplitR; [done|].

  iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod ("Hcont" with "Hσ_t") as (? ?) "[Hσ_t Hm]". iModIntro.
  iSplit; first by eauto with base_step.
  iIntros (??? Hstep) "!>"; inv_base_step.
  iFrame. iSplitR; [done|].
  by iApply "Ht".
Qed.

Lemma source_red_load_sc π l q v Ψ `{!sheapInvSupportsLoad ScOrd}:
  l ↦s{#q} v -∗
  (l ↦s{#q} v -∗ source_red (of_val v) π Ψ) -∗
  source_red (Load ScOrd (Val $ LitV $ LitLoc l)) π Ψ.
Proof.
  iIntros "Hl Ht". iApply source_red_lift_base_step.
  iIntros (?? P_s σ_s ??) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]]".
  iDestruct (heap_ctx_wf with "Hσ_s") as %?.
  iDestruct (heap_read with "Hσ_s Hl") as %[??]. iModIntro.
  assert (∃ e_s' σ_s', base_step P_s (Load ScOrd #l) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with base_step. }
  iExists e_s', σ_s'. iSplit; first by eauto. inv_base_step.
  iModIntro. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_load. }
  by iApply "Ht".
Qed.

Lemma source_red_load_na π l v Ψ q `{!sheapInvSupportsLoad Na1Ord} :
  l ↦s{#q} v -∗
  (l ↦s{#q} v -∗ source_red (of_val v) π Ψ) -∗
  source_red (Load Na1Ord (Val $ LitV $ LitLoc l)) π Ψ.
Proof.
  iIntros "Hl Ht". iApply source_red_step.
  iIntros (?? P_s σ_s ??) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]]".
  iDestruct (heap_ctx_wf with "Hσ_s") as %?.
  iDestruct (heap_read with "Hσ_s Hl") as %[??].
  iModIntro. iExists _, _.
  iSplit. {
    iPureIntro.
    apply: no_forks_step. { apply: base_prim_step. by constructor. }
    apply: no_forks_step. { apply: base_prim_step. constructor. by rewrite lookup_insert_eq. }
    apply: no_forks_refl.
  }
  destruct σ_s => /=. rewrite insert_insert_eq insert_id //. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_load. }
  by iApply "Ht".
Qed.

Lemma target_red_store_sc l v v' Ψ :
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) !>".
  iDestruct (heap_read_1 with "Hσ_t Hl") as %?.
  iSplitR; first by eauto with base_step.
  iIntros (e_t' efs σ_t') "%"; inv_base_step.
  iMod (heap_write with "Hσ_t Hl") as "[$ ?]".
  iFrame. iModIntro. iSplitR; first done.
    by iApply "Hsim".
Qed.

Lemma target_red_store_na l v v' Ψ :
  l ↦t v' -∗
  (l ↦t v -∗ target_red (of_val #()) Ψ) -∗
  target_red (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) Ψ.
Proof.
  iIntros "Hl Hsim". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod (heap_write_na with "Hσ_t Hl") as (?) "[Hσ_t Hcont]". iModIntro.
  iSplit; first by eauto with base_step.
  iIntros (??? Hstep) "!>"; inv_base_step.
  iFrame. iSplitR; [done|].

  iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
  iMod ("Hcont" with "Hσ_t") as (?) "[Hσ_t Hm]". iModIntro.
  iSplit; first by eauto with base_step.
  iIntros (??? Hstep) "!>"; inv_base_step.
  iFrame. iSplitR; [done|].
  by iApply "Hsim".
Qed.

Lemma source_red_store_sc π l v v' Ψ `{!sheapInvSupportsStore ScOrd} :
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) π Ψ) -∗
  source_red (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) π Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_lift_base_step.
  iIntros (?? P_s σ_s ??) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]] !>".
  iDestruct (heap_ctx_wf with "Hσ_s") as %?.
  iDestruct (heap_read_1 with "Hσ_s Hl") as %?.
  assert (∃ e_s' σ_s', base_step P_s (Store ScOrd (Val $ LitV (LitLoc l)) (Val v)) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with base_step. }
  iExists e_s', σ_s'. iSplitR; first done. inv_base_step.
  iMod (heap_write with "Hσ_s Hl") as "[$ ?]".
  iFrame. iModIntro.
  iSplitL "Hinv". { by iApply sheap_inv_store. }
  by iApply "Hsim".
Qed.

Lemma source_red_store_na π l v v' Ψ `{!sheapInvSupportsStore Na1Ord} :
  l ↦s v' -∗
  (l ↦s v -∗ source_red (of_val #()) π Ψ) -∗
  source_red (Store Na1Ord (Val $ LitV (LitLoc l)) (Val v)) π Ψ.
Proof.
  iIntros "Hl Hsim". iApply source_red_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]]".
  iDestruct (heap_ctx_wf with "Hσ_s") as %?.
  iDestruct (heap_read_1 with "Hσ_s Hl") as %?.
  iMod (heap_write with "Hσ_s Hl") as "[Hσ_s Hl]".
  iModIntro. iExists _, _.
  iSplit. {
    iPureIntro.
    apply: no_forks_step. { apply: base_prim_step. by constructor. }
    apply: no_forks_step. { apply: base_prim_step. econstructor. by rewrite lookup_insert_eq. }
    apply: no_forks_refl.
  }
  iDestruct ("Hsim" with "Hl") as "$" => /=.
  rewrite insert_insert_eq. iFrame.
  by iApply sheap_inv_store.
Qed.

(** operational lemmas for calls *)
Lemma target_red_call f fn v Ψ :
  f @t fn -∗
  target_red (apply_func fn v) Ψ -∗
  target_red (Call (Val $ LitV $ LitFn f) (Val v)) Ψ.
Proof.
  iIntros "Hf Hred". iApply target_red_lift_base_step.
  iIntros (?????) "(HP_t & HP_s & Hσ_t & Hσ_s & ?) !>".
  iDestruct (has_prog_has_fun_agree with "HP_t Hf") as %?.
  iSplitR; first by eauto with base_step.
  iIntros (e_t' efs σ_t') "%"; inv_base_step.
  iModIntro. by iFrame.
Qed.

Lemma source_red_call π f fn v Ψ :
  f @s fn -∗
  source_red (apply_func fn v) π Ψ -∗
  source_red (Call (Val $ LitV $ LitFn f) (Val v)) π Ψ.
Proof.
  iIntros "Hf Hred". iApply source_red_lift_base_step.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & ?) [% %]] !>".
  iDestruct (has_prog_has_fun_agree with "HP_s Hf") as %?.
  iExists _, _. iSplit. { simpl. eauto with base_step. }
  iModIntro. iFrame.
  iApply sheap_inv_pure_prim_step; [done| |done] => ??.
  apply: fill_prim_step. apply: base_prim_step. by constructor.
Qed.

(** Call lemmas for sim *)
Lemma sim_call π e_t e_s v_t v_s fname Ψ :
  to_val e_t = Some v_t →
  to_val e_s = Some v_s →
  ⊢ ext_rel π v_t v_s -∗
    (∀ v_t' v_s', ext_rel π v_t' v_s' -∗ Ψ (Val v_t') (Val v_s')) -∗
    Call (f#fname) e_t ⪯{π} Call (f#fname) e_s [{ Ψ }].
Proof.
  intros <-%of_to_val <-%of_to_val.
  iIntros "H Hs". iApply (sim_lift_call with "H"). iApply "Hs".
Qed.

(** fork *)
Lemma sim_fork π e_t e_s Ψ `{!sheapInvSupportsFork} :
  #() ⪯{π} #() [{ Ψ }] -∗
  (∀ π', e_t ⪯{π'} e_s [{ lift_post (ext_rel π') }]) -∗
  Fork e_t ⪯{π} Fork e_s [{ Ψ }].
Proof.
  iIntros "Hval Hsim". iApply sim_lift_base_step_both.
  iIntros (??????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) [% %]] !>".
  iDestruct (heap_ctx_wf with "Hσ_s") as %?.
  iSplitR. { eauto with base_step. }
  iIntros (e_t' efs_t σ_t') "%"; inv_base_step.
  iModIntro. iExists _, _, _. iSplitR. { eauto with base_step. }
  simpl. iFrame.
  iSplitL "Hinv". { by iApply sheap_inv_fork. }
  iSplitL; [|done]. iApply "Hsim".
Qed.

(** Coinduction support *)

Lemma sim_while_while {π b_t b_s c_t c_s} inv Ψ :
  inv -∗
  □ (inv -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{π}
    (if: c_s then b_s ;; while: c_s do b_s od else #())%E
      [{ λ e_t e_s, Ψ e_t e_s ∨ (⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗ inv) }]) -∗
  (while: c_t do b_t od ⪯{π} while: c_s do b_s od [{ Ψ }])%E.
Proof.
  iIntros "Hinv_init #Hstep".
  iApply (sim_lift_coind_pure inv with "[] Hinv_init");
    [apply pure_while | apply pure_while | done.. ].
Qed.

Lemma sim_while_rec {b_t c_t v_s} (inv : val → iProp Σ) (fn_s : func)  Ψ rec_n π :
  inv v_s -∗
  rec_n @s fn_s -∗
  □ (∀ v_s', inv v_s' -∗
    (if: c_t then b_t ;; while: c_t do b_t od else #())%E ⪯{π} (apply_func fn_s v_s')%E
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call f#rec_n (Val v_s')⌝ ∗ inv v_s') }]) -∗
  (while: c_t do b_t od ⪯{π} Call f#rec_n v_s [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_base_coind (λ e_t e_s, (∃ v_s', ⌜e_t = while: c_t do b_t od%E⌝ ∗ ⌜e_s = Call f#rec_n (Val v_s')⌝ ∗ inv v_s')%I)); first last.
  { iExists v_s. eauto. }
  iModIntro. iIntros (e_t e_s P_t P_s σ_t σ_s ??) "He ((?&HP_s&?&?&?) & [% %])". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").
  iModIntro. iSplitR; first by eauto with base_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_base_step.
  iModIntro. iExists (apply_func _ _), σ_s.

  iDestruct (has_prog_has_fun_agree with "HP_s Hrec") as %?.
  iFrame. iSplitR; [done|].
  iSplitR; [by eauto with base_step|].
  iApply sheap_inv_pure_prim_step; [done| |done] => ??.
  apply: fill_prim_step. apply: base_prim_step. by constructor.
Qed.

Lemma sim_rec_while {b_s c_s v_t} (inv : val → iProp Σ) (fn_t : func) Ψ rec_n π :
  inv v_t -∗
  rec_n @t fn_t -∗
  □ (∀ v_t', inv v_t' -∗
    (apply_func fn_t v_t') ⪯{π}  (if: c_s then b_s ;; while: c_s do b_s od else #())
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_t', ⌜e_t = Call f#rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  inv v_t') }]) -∗
  Call f#rec_n v_t ⪯{π} while: c_s do b_s od [{ Ψ }].
Proof.
  iIntros "Hinv #Hrec #Hstep". iApply (sim_lift_base_coind (λ e_t e_s, (∃ v_t', ⌜e_t = Call f#rec_n (Val v_t')⌝ ∗ ⌜e_s = while: c_s do b_s od%E⌝ ∗  inv v_t'))%I); first last.
  { iExists v_t. eauto. }
  iModIntro. iIntros (e_t e_s P_t P_s σ_t σ_s ??) "He ((HP_t & ? & ? & ? &?) & [% %])". iDestruct "He" as (v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").

  iDestruct (has_prog_has_fun_agree with "HP_t Hrec") as %?.
  iModIntro. iSplitR; first by eauto with base_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_base_step.
  iModIntro.
  assert (∃ e_s' σ_s', base_step P_s (while: c_s do b_s od ) σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with base_step. }
  iExists e_s', σ_s'. inv_base_step. iFrame. iSplitR; [done|].
  iSplitR; [by eauto with base_step|].
  iApply sheap_inv_pure_prim_step; [done| |done] => ??.
  apply: fill_prim_step. apply: base_prim_step. by constructor.
Qed.

Lemma sim_rec_rec {v_t v_s} (inv : val → val → iProp Σ) (fn_t fn_s : func)  Ψ rec_t rec_s π :
  inv v_t v_s -∗
  rec_t @t fn_t -∗
  rec_s @s fn_s -∗
  □ (∀ v_t' v_s', inv v_t' v_s' -∗
    (apply_func fn_t v_t') ⪯{π} (apply_func fn_s v_s')
    [{ λ e_t e_s , Ψ e_t e_s ∨ (∃ v_t' v_s', ⌜e_t = Call f#rec_t (Val v_t')⌝ ∗ ⌜e_s = Call f#rec_s (Val v_s')⌝ ∗ inv v_t' v_s') }]) -∗
  ( Call f#rec_t v_t ⪯{π} Call f#rec_s v_s [{ Ψ }])%E.
Proof.
  iIntros "Hinv #Hrec_t #Hrec_s #Hstep".
  iApply (sim_lift_base_coind (λ e_t e_s, (∃ v_t' v_s', ⌜e_t = Call f#rec_t (Val v_t')⌝ ∗ ⌜e_s = Call f#rec_s (Val v_s')⌝ ∗ inv v_t' v_s'))%I); first last.
  { iExists v_t, v_s. eauto. }
  iModIntro. iIntros (e_t e_s P_t P_s σ_t σ_s ??) "He ((HP_t & HP_s & ? & ? &?) & [% %])".
  iDestruct "He" as (v_t' v_s') "(-> & -> & Hinv)".
  iSpecialize ("Hstep" with "Hinv").

  iDestruct (has_prog_has_fun_agree with "HP_t Hrec_t") as %?.
  iDestruct (has_prog_has_fun_agree with "HP_s Hrec_s") as %?.
  iModIntro. iSplitR; first by eauto with base_step.
  iIntros (e_t' efs σ_t') "%Hhead"; inv_base_step.
  iModIntro.
  assert (∃ e_s' σ_s', base_step P_s (Call f#rec_s v_s') σ_s e_s' σ_s' []) as (e_s' & σ_s' & Hred).
  { eauto with base_step. }
  iExists e_s', σ_s'. inv_base_step. iFrame.
  iSplitR; [done|].
  iSplitR; [by eauto with base_step|].
  iApply sheap_inv_pure_prim_step; [done| |done] => ??.
  apply: fill_prim_step. apply: base_prim_step. by constructor.
Qed.
End lifting.
