# Intermediate Memory Model (IMM) and compilation correctness proofs for it

## Related projects
<img align="right" width="350" src="https://github.com/anlun/publicFiles/raw/master/pictures/spider.png">

- A **Promising 1.0** [Kang-al:POPL17] to IMM compilation correctness proof [[Github](https://github.com/weakmemory/promising1ToImm)]
- A **Promising 2.0** [Lee-al:PLDI20] to IMM compilation correctness proof [[Github](https://github.com/weakmemory/promising2ToImm)]
- A **Weakestmo** [Chakraborty-Vafeiadis:POPL19] to IMM compilation correctness proof [[Github](https://github.com/weakmemory/weakestmoToImm)]

## Related papers

- **[POPL19]** *Bridging the Gap Between Programming Languages and Hardware Weak Memory Models*
  <br />
  [[Paper](https://doi.org/10.1145/3290382) | [arXiv](https://arxiv.org/abs/1807.07892) |
[POPL19 arifact release](https://doi.org/10.5281/zenodo.1484024)]
  <br />
  Anton Podkopaev, Ori Lahav, and Viktor Vafeiadis
- **[PLDI20]** *Repairing and Mechanising the JavaScript Relaxed Memory Model*
  <br />
  Conrad Watt, Christopher Pulte, Anton Podkopaev, Guillaume Barbier, Stephen Dolan, Shaked Flur, Jean Pichon-Pharabod, and Shu-yu Guo
- **[CoRR19]** *Reconciling Event Structures with Modern Multiprocessors*
  <br />
  [[arXiv](https://arxiv.org/abs/1911.06567) | [Related project](https://github.com/weakmemory/weakestmoToImm)]
  <br />
  Evgenii Moiseenko, Anton Podkopaev, Ori Lahav, Orestis Melkonian, and Viktor Vafeiadis

## Building the Project

### Requirements
* [Coq](https://coq.inria.fr)
* [Our fork](https://github.com/weakmemory/hahn) of [the Hahn library](https://github.com/vafeiadis/hahn)
* [HahnExt library](https://github.com/weakmemory/hahnExt)
* [The Coq supplementary library w/ basic data types](https://github.com/snu-sf/promising-lib)
To check precise requirements with version numbers, please, check [the Nix configuration file](.nix/config.nix).

### Building via Nix (preferred and mainly supported way)
First, you need to install Nix (see https://nixos.org/download.html) and set-up Nix as recommended by [Coq Nix Toolbox](https://github.com/coq-community/coq-nix-toolbox).
That is, run
```
nix-env -iA nixpkgs.cachix && cachix use coq && cachix use coq-community && cachix use math-comp
```
in order to use binary caches from recognized organizations.
Additionally, we recommend add our binary cache with IMM and related packages as well:
```
cachix use weakmemory
```
Then, you may just run `nix-build` in the root folder of the project to build it.
Alternatively, you may run `nix-shell` and then, in the Nix-configured environment, run `make -j`.

#### Working on the project in VS Code
You may use the [Nix Environment Selector](https://marketplace.visualstudio.com/items?itemName=arrterian.nix-env-selector) plugin in VS Code for it to use proper configuration.
Alternatively, 
you may run `nix-shell` in the root of the project and then `code .`--VSCoq or CoqLSP should be able to pick up the environment.
 
### Building Manually (supported up to the 1.5 version of IMM)

To build the project, one needs to install libraries (`promising-lib`, `hahn`, `hahnExt`), which the project
depends on.
This might be done by running `./configure`.
The command installs `Coq` as well. After that, one needs to run `make` (or `make -j4` for a faster build).

### Installation via OPAM (supported up to the 1.5 version of IMM)
The project may be built and installed via OPAM:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-promising-local -k git https://github.com/snu-sf/promising-opam-coq-archive
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm
```

## Description of code and its relation to the **[POPL19]** paper
* **Section 2.** `src/basic`. Definitions and statements about programs and execution graphs.
  - *Prog.v*—a definition of the program language (**Fig. 2**).
  - *Events.v*—definitions related to events (**Section 2.2**).
  - *Execution.v*, *Execution\_eco.v*—execution graphs (**Section 2.2**).
  - *ProgToExecution.v*—construction of execution graphs from sequential programs (**Fig. 3**).
  - *ProgToExecutionProperties.v*—properties of the construction.

* **Section 3.** `src/imm`. Definitions and statements about IMM
and IMMs, a version of IMM with RC11-style definition of happens-before (HB) (**Section 7.0**).
  - *CombRelations.v*, *CombRelationsMore.v*—definitions of relation VF (in the development called `furr`)
     and linked relations and their properties.
  - *imm\_common\_more.v*, *imm\_common.v*—common definitions for both models.
  - *imm\_hb.v*—a definition of HB for IMM (**Section 3.1**).
  - *imm\_s\_hb.v*—the RC11-style definition of HB for IMMs.
  - *imm.v*—a definition of IMM (**Def. 3.11**).
  - *imm\_s.v*—a definition of IMMs (**Section 7.0**).
  - *imm\_sToimm.v*—a proof that IMMs is weaker than IMM.

* **Section 4.** `src/hardware`. Definitions of hardware models and proofs about them.
  - *Power\_fences.v*,
    *Power\_ppo.v*,
    *Power.v*—a definition of POWER (Alglave-al:TOPLAS14).
  - *Rel\_opt.v*—a correctness proof for release write transformation (**Thm. 4.1**).
  - *immToPower.v*—a compilation correctness proof from IMM to POWER (**Thm. 4.3**).
  - *Arm.v*—a definition of ARMv8.3 (Pulte-al:POPL18).
  - *immToARM.v*—a compilation correctness proof from IMM to ARMv8.3 (**Thm. 4.5**).
  - *TSO.v*—a definition of TSO (Alglave-al:TOPLAS14, Owens-al:TPHOLs09).
  - *immToTSO.v*—a compilation correctness proof from IMM to TSO.

* **Section 5.** `src/c11`. Definition of a (stronger) version of the C11 model w/o SC and NA accesses and a compilation correctness proof from it to IMMs.
  - *C11.v*—a definition of the stronger version of the C11 model (Batty-al:POPL11). The version follows a fix from Lahav-al:PLDI17.
  - *C11Toimm\_s.v*—a compilation correctness proof from C11 to IMMs.

* **Section 5.** `src/rc11`. Definition of the RC11 model w/o SC and NA accesses and a compilation correctness proof from it to IMMs.
  - *RC11.v*—a definition of RC11 (Lahav-al:PLDI17).
  - *RC11Toimm\_s.v*—a compilation correctness proof from RC11 to IMMs.
  
* **Sections 6.2 and 7.2** `src/traversal`. Traversal of IMM-consistent graphs.
  - *TraversalConfig.v*, *Traversal.v*—a small traversal step of IMMs-consistent execution graphs
      used to prove properties of the traversal (**Def. 7.3 and 7.7**).
  - *SimTraversal.v*—traversal of IMMs-consistent execution graphs (**Prop. 6.5**).
  - *SimTraversalProperties.v*—properties of the normal traversal.
  
* **New parts:** `src/travorder`. Traversal of IMM-consistent graphs based on the traversal labels approach.
  - *TraversalOrder.v*—definitions of traversal labels and relation describing the restrictions on the traversal order.
  - *TLSCoherency.v*—definitions of coherent sets of traversal labels.
  - *IordCoherency.v*—definition of a traversal labels set corresponding to a traversal prefix.
  - *SimClosure.v*—transitions between traversal labels set corresponding to simulation steps.
  - *SimClosureTraversal.v*—construction of a traversal.
  
  
Auxiliary files:
- *IfThen.v*,
*TraversalConfigAlt.v*,
*TraversalCounting.v*,
*ViewRelHelpers.v*.
