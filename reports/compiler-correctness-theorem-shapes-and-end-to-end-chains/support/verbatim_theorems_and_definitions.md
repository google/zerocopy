<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Verbatim Top-Level Compiler-Correctness Theorems and Supporting Definitions

This support file preserves the exact top-level theorem statements and the
core semantic definitions they depend on across the 15 examined verified
compiler and binary-verification precedents at their pinned revisions.

## 1. CompCert 3.18 (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`)

### 1.1 `common/Events.v` (blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`, lines 42-112, 232-310)

```coq
Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVlong: int64 -> eventval
  | EVfloat: float -> eventval
  | EVsingle: float32 -> eventval
  | EVptr_global: ident -> ptrofs -> eventval.

Inductive event: Type :=
  | Event_syscall: string -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_annot: string -> list eventval -> event.

Definition trace := list event.
Definition E0 : trace := nil.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Definition extcall_sem : Type :=
  Senv.t -> list val -> mem -> trace -> val -> mem -> Prop.
```

### 1.2 `common/Behaviors.v` (blob `822b08832f491e82fefc5b60251c13a63ef71301`, lines 35-145)

```coq
Inductive program_behavior: Type :=
  | Terminates: trace -> int -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

Inductive state_behaves (L: semantics) (s: state L): program_behavior -> Prop :=
  | state_terminates: forall t s' r,
      Star L s t s' ->
      final_state L s' r ->
      state_behaves L s (Terminates t r)
  | state_diverges: forall t s',
      Star L s t s' ->
      Forever_silent L s' ->
      state_behaves L s (Diverges t)
  | state_reacts: forall T,
      Forever_reactive L s T ->
      state_behaves L s (Reacts T)
  | state_goes_wrong: forall t s',
      Star L s t s' ->
      nostep L s' ->
      (forall r, ~final_state L s' r) ->
      state_behaves L s (Goes_wrong t).

Inductive program_behaves (L: semantics): program_behavior -> Prop :=
  | program_runs: forall s beh,
      initial_state L s -> state_behaves L s beh ->
      program_behaves L beh
  | program_goes_initially_wrong:
      (forall s, ~initial_state L s) ->
      program_behaves L (Goes_wrong E0).

Definition behavior_improves (beh1 beh2: program_behavior) : Prop :=
  beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.
```

### 1.3 `common/Smallstep.v` (blob `cefab134fdce4f3ea2f970db49a99d987c05d3a1`, lines 1274-1324, 1863-1866)

```coq
Definition safe (L: semantics) (s: state L) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists t, exists s'', Step L s' t s'').

Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ match_states i s1' s2;
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
    bsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

Inductive backward_simulation (L1 L2: semantics) : Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (match_states: index -> state L1 -> state L2 -> Prop)
                      (props: bsim_properties L1 L2 index order match_states).

Lemma forward_to_backward_simulation:
  forall L1 L2,
  forward_simulation L1 L2 -> receptive L1 -> determinate L2 ->
  backward_simulation L1 L2.
```

### 1.4 `driver/Compiler.v` (blob `60fc74fec1411216425004f6d63567354e146e9c`, lines 446-473) and `driver/Complements.v` (blob `d3974c2f7c2e5d04f2a3293fa6cfdb1215e5a217`, lines 50-98)

```coq
Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation (Csem.semantics c_program) (Asm.semantics asm_program).

Theorem transf_c_program_preservation:
  forall p tp beh,
  transf_c_program p = OK tp ->
  program_behaves (Asm.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
```

## 2. CompCertO, CompCertM, CompCertTSO, CASCompCert, Stack-Aware CompCert, and Quantitative CompCert

### 2.1 CompCertO (Koenig & Shao, POPL 2021, DOI `10.1145/3453483.3454097`, `SJTU-PLV/CompCert@e3d03ed822a7aaf452b7022c347187ed1efc1c12`, `common/Smallstep.v:1572-1603`)

```coq
Record callconv (liA liB: language_interface) : Type := {
  ccworld : Type;
  match_senv: ccworld -> Senv.t -> Senv.t -> Prop;
  match_query: ccworld -> query liA -> query liB -> Prop;
  match_reply: ccworld -> reply liA -> reply liB -> Prop
}.

Theorem clight_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  fsim (ro @ c_injp @ wt_c @ ca_injp) (Clight.semantics2 p) (Asm.semantics tp).
```

### 2.2 Stack-Aware CompCert (`ssrg-vt/compcert_stack_aware@0518d9ffb69ec11e79a214df1afc0b0159930478`, POPL 2019 DOI `10.1145/3290382`, `driver/Compiler.v`)

```coq
Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  forall (StackSize: Z),
  0 <= StackSize <= Ptrofs.max_unsigned ->
  backward_simulation (Csem.semantics p StackSize) (Asm.semantics tp StackSize).
```

## 3. CakeML (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`)

### 3.1 `semantics/ffi/ffiScript.sml` (blob `b40698d34360646ffb56e098e15571f99b99d9f4`) and `compiler/proofs/compilerProofScript.sml` (blob `c3184fe7a19850c9b8a9a73abe7090c2b9342948`, lines 269-295)

```hol
Datatype:
  final_event = Terminate outcome (io_event list)
              | Diverge (io_event llist)
              | Fail
End

Definition extend_with_resource_limit_def:
  extend_with_resource_limit behaviours =
    behaviours UNION
    { Terminate Resource_limit_hit io_list |
      ?t outcome ws.
        Terminate outcome ws IN behaviours /\ (io_list <<= ws) \/
        Diverge t IN behaviours /\ LPREFIX (fromList io_list) t }
End

Theorem compile_correct:
  !st env prog cc cbspace data_sp bytes bitmaps1 ffi_names1 mc ms.
    compile cc prog = SOME (bytes, bitmaps1, ffi_names1) /\
    config_ok cc mc /\
    ~semantics_prog st env prog Fail /\
    installed bytes cbspace bitmaps1 data_sp ffi_names1
      (heap_regs cc.backend_config.stack_conf.reg_names) mc st.ffi ms
    ==>
    machine_sem mc st.ffi ms SUBSET
      extend_with_resource_limit (semantics_prog st env prog)
Proof
```

## 4. CertiCoq / CertiRocq, Œuf, Pilsner, Bedrock2, Vale, Jasmin, and seL4 (`graph-refine`)

### 4.1 CertiRocq (`CertiRocq/certirocq@906241771e0ac0088403dec12a0027213f114dd1`, `theories/Compiler/correctness.v:122-150`, `theories/LambdaBox_to_LambdaANF/anf_toplevel.v:143-149`)

```coq
Definition refines (e_src : env_src * term_src) (e_tgt : term_tgt) : Prop :=
  forall v_src f_src t_src,
     eval_src (fst e_src) (snd e_src) v_src f_src t_src ->
     exists v_tgt c_tgt,
       eval_tgt e_tgt c_tgt (Res v_tgt) /\
       (c_tgt <= t_src + M)%nat /\
       value_ref v_src v_tgt.
```

### 4.2 Œuf (`uwplse/oeuf@f3e4d236465ba872d1f1b8229548fa0edf8f7a3f`, `src/Oeuf.v:374-378`, `src/OeufProof.v`)

```coq
Theorem transf_whole_program_correct :
  forall cu shim tprog,
    transf_whole_program cu shim = OK tprog ->
    exists prog,
      link_cu_shim cu shim = Some prog /\
      backward_simulation (SourceL.semantics cu) (Asm.semantics tprog).
```

### 4.3 Bedrock2 (`mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13`, `compiler/src/compiler/Pipeline.v:112-195`)

```coq
Theorem compiler_correct:
  forall (functions : list (string * (list string * list string * cmd)))
         (insts : list Instruction) (f_entry_rel_pos : Z) (required_stack_space : Z)
         (initial : RiscvMachine) (post : trace -> mem -> Prop),
    compile compile_ext_call (map.of_list functions) = Some (insts, f_entry_rel_pos, required_stack_space) ->
    required_stack_space <= word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word ->
    exec (map.of_list functions) main_body initial.(getLog) initial_mem map.empty post ->
    runsTo (mcomp_sat (run1 iset)) initial
      (fun final => exists final_mem, post final.(getLog) final_mem).
```

### 4.4 Jasmin (`jasmin-lang/jasmin@34f15840f10625bbc2cbf59b3d877e94c75bfbd9`, `proofs/compiler/it_compiler_proof.v:1688`)

```coq
Lemma it_compile_prog_to_asmP (entries : seq funname) (p : uprog) (xp : asm_prog) :
  compile_prog_to_asm aparams cparams entries p = ok xp ->
  forall fn, fn \in entries ->
  exists fd xfd,
    get_fundef (p_funcs p) fn = Some fd /\
    get_fundef (asm_funcs xp) fn = Some xfd /\
    wkequiv_io (full_pre aparams cparams fd xfd)
               (isem_unit (p_Initialize p) fn)
               (isem_asm xp fn)
               (full_post aparams cparams fd xfd).
```

### 4.5 seL4 (`seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`, `proof/crefine/Refine_C.thy` & `seL4/graph-refine@94c93d18830d680fc6732d21fb16ca58ebca9dc5`)

```isabelle
theorem corres_Underlying_CRT:
  "\<lbrakk> einvs s; valid_sched s; ... \<rbrakk> \<Longrightarrow>
   corres_underlying rf_sr True True dc (einvs and valid_sched) \<top>
     (callKernel ev) (callKernel_C ev)"
```
