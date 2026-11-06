From simuliris.stacked_borrows Require Export notation defs.
From simuliris.stacked_borrows Require Import steps_progress steps_retag.

Lemma head_free_inv (P : prog) l bor T σ σ' e' efs :
  base_step P (Free (PlaceR l bor T)) σ e' σ' efs →
  ∃ α',
    memory_deallocated σ.(sst) σ.(scs) l bor (tsize T) = Some α' ∧
    (∀ m : Z, is_Some (shp σ !! (l +ₗ m)) ↔ 0 ≤ m < tsize T) ∧
    e' = #[☠]%E ∧
    σ' = mkState (free_mem l (tsize T) σ.(shp)) α' σ.(scs) σ.(snp) σ.(snc) ∧
    efs = [].
Proof. intros Hhead. inv_base_step. eauto 8. Qed.

Lemma head_copy_inv (P : prog) l t T σ e σ' efs :
  base_step P (Copy (PlaceR l t T)) σ e σ' efs →
  efs = [] ∧
  ((∃ v α', read_mem l (tsize T) (shp σ) = Some v ∧
  memory_read (sst σ) (scs σ) l t (tsize T) = Some α' ∧
  (*v <<t snp σ ∧*)
  σ' = mkState (shp σ) α' (scs σ) (snp σ) (snc σ) ∧
  e = (ValR v)) ∨
  e = ValR (replicate (tsize T) ScPoison) ∧ memory_read (sst σ) (scs σ) l t (tsize T) = None ∧ σ' = σ).
Proof. intros Hhead. inv_base_step; first by eauto 10. destruct σ; eauto 10. Qed.

Lemma head_write_inv (P : prog) l bor T v σ σ' e' efs :
  base_step P (Write (Place l bor T) (Val v)) σ e' σ' efs →
  ∃ α',
  efs = [] ∧
  e' = (#[ScPoison])%E ∧
  σ' = mkState (write_mem l v σ.(shp)) α' σ.(scs) σ.(snp) σ.(snc) ∧
  length v = tsize T ∧
  (∀ i : nat, (i < length v)%nat → l +ₗ i ∈ dom σ.(shp)) ∧
  memory_written σ.(sst) σ.(scs) l bor (tsize T) = Some α'.
Proof. intros Hhead. inv_base_step. eauto 9. Qed.

Lemma head_retag_inv (P : prog) σ σ' e' efs l ot c pkind T rkind :
  base_step P (Retag #[ScPtr l ot] #[ScCallId c] pkind T rkind) σ e' σ' efs →
  ∃ nt α' nxtp',
  retag σ.(sst) σ.(snp) σ.(scs) c l ot rkind pkind T = Some (nt, α', nxtp') ∧
  e' = (#[ScPtr l nt])%E ∧
  efs = [] ∧
  σ' = mkState σ.(shp) α' σ.(scs) nxtp' σ.(snc) ∧
  c ∈ σ.(scs).
Proof. intros Hhead. inv_base_step. eauto 8. Qed.

Lemma head_init_call_inv (P : prog) e' σ σ' efs :
  base_step P InitCall σ e' σ' efs →
  ∃ c,
    c = σ.(snc) ∧
    efs = [] ∧
    e' = (#[ScCallId c])%E ∧
    σ' = (mkState σ.(shp) σ.(sst) ({[ σ.(snc) ]} ∪ σ.(scs)) σ.(snp) (S σ.(snc))).
Proof. intros Hhead. inv_base_step. eauto. Qed.

Lemma head_end_call_inv (P : prog) e' σ σ' efs c :
  base_step P (EndCall #[ScCallId c]) σ e' σ' efs →
  c ∈ σ.(scs) ∧
  efs = [] ∧
  e' = (#[☠])%E ∧
  σ' = state_upd_calls (.∖ {[ c ]}) σ.
Proof. intros Hhead. inv_base_step. eauto. Qed.

Lemma head_alloc_inv (P : prog) T σ σ' e' efs :
  base_step P (Alloc T) σ e' σ' efs →
  let l := (fresh_block σ.(shp), 0) in
  efs = [] ∧
  e' = Place l (Tagged σ.(snp)) T ∧
  σ' = mkState (init_mem l (tsize T) σ.(shp)) (init_stacks σ.(sst) l (tsize T) (Tagged σ.(snp))) σ.(scs) (S σ.(snp)) σ.(snc).
Proof. intros Hhead. inv_base_step. eauto. Qed.
