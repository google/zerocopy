# Simuliris Coq development

This repository contains the Coq development of Simuliris (paper presented at POPL22: https://iris-project.org/pdfs/2022-popl-simuliris.pdf).
It also contains the proofs for [Tree Borrows](theories/tree_borrows/README.md).

## Prerequisites

This version is known to compile with:

 - Rocq 9.2.0
 - A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)
 - A recent version of [Coq-Equations](https://github.com/mattam82/Coq-Equations)

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for
installing the dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

## Structure

The project follows the following structure below the `theories` folder:
- `logic` and `base_logic` contain libraries for defining fixpoints as well as general ghost state constructions.
- `simulation` contains the language-generic parts of the framework, in particular the definition of the simulation relation and the general adequacy proof.
    * `language.v` contains our generic language interface.
    * `slsls.v` defines the simulation relation, weakest preconditions for source and target, and general rules for them.
    * `lifting.v` contains general lifting lemmas as well as the definition of the generic "source-safety" judgment for exploiting UB.
    * `closed_sim.v` contains the definition of the closed simulation (removing the call case) used in the adequacy proof.
    * `behavior.v` defines our notion of behavioral refinement and whole-program refinement.
    * `fairness.v` defines our notion of fairness and proves it equivalent to alternative definitions that are crucial for the fairness proof.
    * `fairness_adequacy.v` proves that the simulation relation is fair termination-preserving.
    * `adequacy.v` plugs this all together and shows that Simuliris's simulation in separation logic implies a meta-level simulation, and then derives our general adequacy statement.
    * `gen_log_rel.v` defines a language-generic version of our logical relation on open terms.
- `simulang` contains the definition of SimuLang and our program logics and examples for it.
   We have defined two program logics for SimuLang: a "simple" one without support for exploiting non-atomics, and a version extended with support for exploiting non-atomics.
    * `lang.v` contains the definition of SimuLang and its operational semantics, as well as its instantiation of the language interface.
    * `logical_heap.v` contains the ghost state for the heap.
    * `heapbij.v` contains the heap bijection ghost state that is used for both program logics.
    * `globalbij.v` contains support for global variables.
    * `primitive_laws.v` instantiates the simulation relation with SimuLang. It is parametric over an additional invariant on the state and proves basic proof rules for SimuLang.
    * `gen_val_rel.v` defines a generic value relation for SimuLang that is used by both program logics, but parametric over the notion of relatedness for locations.
    * `log_rel_structural.v`, `gen_refl.v`, and `pure_refl.v` contain conditions on the logical relation as well as general reflexivity proofs used by both program logics.
    * `behavior.v` defines our notion of behavior and contextual refinement for SimuLang.
    * `simple_inv` contains the simple program logic, with no support for exploiting non-atomics.
        + `inv.v` contains the invariant on the state (mainly the bijection, which does not allow to take out ownership) and basic laws.
        + `refl.v` contains the reflexivity theorem.
        + `adequacy.v` derives the adequacy proof of the logical relation (i.e., that it implies contextual refinement).
        + `examples` contains examples using this logic, see below for a list.
    * `na_inv` contains the non-atomic program logic, with added support for exploiting non-atomics.
        + `na_locs.v` contains the pure invariants and reasoning about data races.
        + `inv.v` contains the invariant on the state (allowing to take out ownership from the bijection), basic laws, and rules for exploiting non-atomic accesses.
        + `refl.v` contains the reflexivity theorem.
        + `adequacy.v`  derives the adequacy proof of the logical relation (i.e., that it implies contextual refinement).
        + `readonly_refl.v` contains a reflexivity theorem for read-only expressions which allows to thread through ownership of exploited locations.
        + `examples` contains examples using this logic, see below for a list.
- `stacked_borrows` contains the port of the Stacked Borrows language and optimizations to Simuliris.
    * `lang_base.v`, `expr_semantics.v`, `bor_semantics.v`, and `lang.v` contain the language definition.
    * `logical_state.v` defines the invariants and instantiates the simulation relation.
    * `steps_refl.v` and `steps_opt.v` prove the main execution lemmas.
    * `behavior.v` defines the notion of contextual refinement and expression well-formedness.
    * `adequacy.v` contains the resulting adequacy proof.
    * `examples` contains example optimizations, see below.
- `tree_borrows` contains the Simuliris development of Tree Borrows.
  This development has its [own README](theories/tree_borrows/README.md).


## Theorems, definitions, and examples referenced in the paper

We list the relevant theorems and definitions mentioned in the paper by section.

### Section 2

| Paper | Coq file | Coq name |
| ------ | ------ | ------ |
| SimuLang grammar (Figure 2) | `theories/simulang/lang.v` | `expr`, `val`, `prog`, `ectx_item`, `ectx` |
| Example from 2.1 | `theories/simulang/simple_inv/examples/paper.v` | `ex_2_1` |
| Hoare triples and quadruples from Figure 3 | `theories/simulang/simple_inv/examples/derived.v` | (replace dashes by underscores) |
| Example 1 from 2.2 | `theories/simulang/simple_inv/examples/paper.v` | `ex_2_2_1` |
| Example 2 from 2.2 | `theories/simulang/simple_inv/examples/paper.v` | `ex_2_2_2` |
| Value relation (Figure 4) | `theories/simulang/simple_inv/inv.v` | `val_rel` |
| Rule `loc-escape` (2.2) | `theories/simulang/simple_inv/examples/derived.v` | `sim_insert_bij` |
| Rule `sim-load-escaped` (2.2) | `theories/simulang/simple_inv/examples/derived.v` | `sim_load_public` |
| Rule `sim-src-safe` (2.3) | `theories/simulang/simple_inv/examples/derived.v` | `sim_src_safe` |
| Rule `safe-div-int-nonzero` (2.3) | `theories/simulang/simple_inv/examples/derived.v` | `safe_div_int_nonzero` |
| Example from 2.3 | `theories/simulang/simple_inv/examples/paper.v` | `ex_2_3` |
| Example from 2.4 | `theories/simulang/simple_inv/examples/paper.v` | `ex_2_4` |
| Rule `while-coind` (2.4) | `theories/simulang/simple_inv/examples/derived.v` | `sim_while_simple` |
| Rule `while-paco` (2.4) | `theories/simulang/simple_inv/examples/derived.v` | `sim_while` |

### Section 3

| Paper | Coq file | Coq name |
| ------ | ------ | ------ |
| Rule `exploit-store` (Figure 7) | `theories/simulang/na_inv/examples/derived.v` | `sim_exploit_store` |
| Rule `exploit-load` (Figure 7) | `theories/simulang/na_inv/examples/derived.v` | `sim_exploit_load` |
| Rule `release-exploit` (Figure 7) | `theories/simulang/na_inv/examples/derived.v` | `sim_exploit_release` |
| Example from 3.2 | `theories/simulang/na_inv/examples/paper.v` | `load_na_sc_sim`, `load_na_sc_log`, and `load_na_sc_ctx` |
| Example from 3.2 with arbitrary read-only expressions (footnote 8) | `theories/simulang/na_inv/examples/paper.v` | `load_na_log`, and `load_na_ctx` |
| Example from 1,3.3 | `theories/simulang/na_inv/examples/paper.v` | `hoist_load_both_log`, `hoist_load_both_ctx` |
| Example from 1,3.3 with memory deallocation | `theories/simulang/na_inv/examples/data_races.v` | `hoist_load_both_log`, `hoist_load_both_ctx` | 
| Rules in Figure 8| `theories/simulang/na_inv/examples/derived.v` | `sim_load_sc_public`, `sim_load_na_public`, `sim_store_sc_public`, `sim_call` |

### Section 4

The definition of contextual refinement is language-specific as the contexts are language-specific.
Similarly, the specific logical relation is specific to the different program logics
(although we have factored out a common structure and other common components that can be re-used in a language-generic way,
 see `theories/simulation/gen_log_rel.v`).
They are instantiated for the fundamental theorems.
| Paper | Coq file | Coq name |
| ------ | ------ | ------ |
| Possible behaviors `ℬ` | `theories/simulation/behavior.v` | `has_beh` |
| Behavioral refinement `⊑_beh` | `theories/simulation/behavior.v` | `beh_ref` |
| program refinement `⊑_prog` | `theories/simulation/behavior.v` | `prog_ref_alt` |
| Contextual refinement `⊑_ctx` (language-specific), SimuLang | `theories/simulang/behavior.v` | `ctx_ref` |
| Logical relation `≤_log` (SimuLang, generic) | `theories/simulang/log_rel_structural.v` | `log_rel` |
| Theorem 4.1 (for SimuLang, non-atomic logic) | `theories/simulang/na_inv/refl.v` | `log_rel_refl` |
| Theorem 4.2 (for SimuLang, non-atomic logic) | `theories/simulang/na_inv/refl.v` | `log_rel_ctx` |
| Theorem 4.3 (for SimuLang, non-atomic logic) | `theories/simulang/na_inv/adequacy.v` | `log_rel_adequacy` |

### Section 5

| Paper | Coq file | Coq name |
| ------ | ------ | ------ |
| Simulation relation (Figure 11) (full version) | `theories/simulation/slsls.v` | `greatest_def`, `sim_expr_inner` |
| Hoare quadruple definition | `theories/simulang/hoare.v` | `hoareSim`|
| source safety judgment `e_s ⇝ Q` (generalized) | `theories/simulation/lifting.v` | `SafeImplies` |
| whole-program relation `≤_prog` | `theories/simulation/gen_log_rel.v` | `prog_rel` |
| Lemma 5.1 | `theories/simulation/adequacy.v` | `slsls_adequacy` |
| program refinement `⊑_prog` | `theories/simulation/behavior.v` | `prog_ref_alt` |
| closed simulation (proof of Lemma 5.1) | `theories/simulation/closed_sim.v` | `csim_expr_inner`, `closed_greatest_def` |
| Theorem 5.2 (for SimuLang, non-atomic logic) | `theories/simulang/na_inv/adequacy.v` | `log_rel_adequacy` |
| Theorem 5.2 (for SimuLang, simple logic) | `theories/simulang/simple_inv/adequacy.v` | `log_rel_adequacy` |

### Section 6

| Paper | Coq file | Coq name |
| ------ | ------ | ------ |
| heapbij (simplified) | `theories/simulang/heapbij.v` | `heapbij_interp` |
| P_h for simple state interpretation | `theories/simulang/simple_inv/inv.v` | `simple_inv` |
| P_h for non-atomic state interpretation | `theories/simulang/na_inv/na_locs.v` | `alloc_rel_pred` |
| exploit_wf (simplified) | `theories/simulang/na_inv/na_locs.v` | `na_locs_wf` |
| state interpretation for non-atomics | `theories/simulang/na_inv/inv.v` | `na_bij_interp` |
| proof of exploit-store | `theories/simulang/na_inv/inv.v` | `sim_bij_exploit_store` |
| preservation for sim-store-sc (Maintaining the state interpretation) | `theories/simulang/na_inv/na_locs.v` | `na_locs_wf_store` |

### Section 7

| Paper | Coq file | Coq name |
| ------ | ------ | ------ |
| Adequacy (Theorem 5.2 for Stacked Borrows) | `theories/stacked_borrows/adequacy.v` | `log_rel_adequacy` |
| Loop example (Fig 12b) | `theories/stacked_borrows/examples/coinductive.v` | `sim_loop_ctx` |
| Moving read example (Fig 12a) | `theories/stacked_borrows/examples/opt1.v` | `sim_opt1'`, `sim_opt1'_ctx` |

The optimizations ported and extended to concurrency from the original Stacked Borrows paper can be found in the following files:
* `theories/stacked_borrows/examples/opt1.v`
* `theories/stacked_borrows/examples/opt1_down.v`
* `theories/stacked_borrows/examples/opt2.v`
* `theories/stacked_borrows/examples/opt2_down.v`
* `theories/stacked_borrows/examples/opt3.v`
* `theories/stacked_borrows/examples/opt3_down.v`

### Section 8

As mentioned in the related work section, we have verified the reorderings and eliminations by [Ševčík, 2011]. They can be found in file `theories/simulang/na_inv/examples/program_transformations_in_weak_memory_models.v`.
For further information on this, we refer to Section 5 of the technical appendix.
