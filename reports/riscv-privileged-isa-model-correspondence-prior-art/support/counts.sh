#!/usr/bin/env bash
# Source-count probe for the riscv-privileged-isa-model-correspondence-prior-art report.
# Self-contained: clones each subject (blob-less, no checkout) into $WORK and reads
# files only at the pinned revisions via `git show <rev>:<path>`.
# Usage: WORK=/tmp/rvpriv-src bash counts.sh
set -u
WORK=${WORK:-/tmp/rvpriv-src}
mkdir -p "$WORK"
clone() { # clone <owner/repo> <dir>
  [ -d "$WORK/$2/.git" ] || git clone -q --filter=blob:none --no-checkout "https://github.com/$1" "$WORK/$2"
}
show() { git -C "$WORK/$1" show "$2:$3"; }

ZK=6810fc14d9c40373101321cefaec59df8d82e3e7
RL_OLD=7c6b500c1744f40d928fb131125cd06edf9f4fce
RL_NEW=0e3365ac7b670d79d70e9b4a8b7fba782607c44f
SRL=51c635c460125ac87955d061fcd902ce03b8011f
SAIL_FIX=e55d89e79e3e5dfa88a137c73be371fb3671c983
MIR=f5ab1955192833ac025a6719a71c6e36a3f643ab
SC=8c238f4103ce43b00078c7b3dc909f7dae05bfc4
SERVAL=72adc4952a1e62330aea527214a26bd0c09cbd05
ISL=c978e10f50db5c40f0fdf113f5f76a779782c6f9
L4V=b0fe7693ca5943e08c49e038d33fd64dc7dfa72e
IBEX=f5b1439295048c6eead73ad4ef8a55cc564e7d6f
ACE=42cf582eef21f9ab661ec7008d65c6de141b4be1
XV6=5cb9df992c45829f6210b3e4176962d7b7a4c408

clone Verified-zkEVM/riscv-zkvm riscv-zkvm
clone opencompl/riscv-lean riscv-lean
clone opencompl/sail-riscv-lean sail-riscv-lean
clone rems-project/sail sail
clone CharlyCst/miralis miralis
clone CharlyCst/softcore-rs softcore-rs
clone uw-unsat/serval serval
clone rems-project/islaris islaris
clone seL4/l4v l4v
clone lowRISC/ibex ibex
clone IBM/ACE-RISCV ace
clone mit-pdos/xv6iris xv6iris

echo "== riscv-zkvm $ZK"
SE=RiscvZkvm/Rv64/SailEquiv
files=$(git -C $WORK/riscv-zkvm ls-tree --name-only $ZK $SE/ | grep '\.lean$')
all=$(for f in $files; do show riscv-zkvm $ZK $f; done)
echo "distinct *_sail_equiv* theorem names: $(echo "$all" | grep -o 'theorem [A-Za-z_0-9]*_sail_equiv[A-Za-z_0-9]*' | sort -u | wc -l)"
echo "base instructions: $(echo "$all" | grep -o 'theorem [A-Za-z_0-9]*_sail_equiv[A-Za-z_0-9]*' | sed -E 's/theorem //; s/_step_sail_equiv/_sail_equiv/; s/_sail_equiv_of_present/_sail_equiv/' | sort -u | wc -l)"
show riscv-zkvm $ZK $SE/StepSim.lean | grep -n -A2 '^def Instr.simulable '
show riscv-zkvm $ZK $SE/VmemReduction.lean | sed -n '956,971p'
show riscv-zkvm $ZK $SE/StepRun.lean | sed -n '77,81p'
show riscv-zkvm $ZK $SE/StepRun.lean | grep -n 'theorem sailStep_run_sim\|theorem sailStepN_run_sim\|theorem jalr_sideCond_satisfiable'
echo "StepRun.lean lines: $(show riscv-zkvm $ZK $SE/StepRun.lean | wc -l)"
show riscv-zkvm $ZK $SE/StateRel.lean | grep -n '^structure StateRel\|^structure StateRelPC\|^structure PlatformFrame'
show riscv-zkvm $ZK RiscvZkvm/Rv64/Execution.lean | sed -n '344,348p'
show riscv-zkvm $ZK scripts/AxiomSweep.lean | sed -n '47,52p'
show riscv-zkvm $ZK RiscvZkvm/Sail/SysControl.lean | sed -n '392,394p'
show riscv-zkvm $ZK docs/validation.md | sed -n '56p;66p;117,120p;133,137p'

echo; echo "== opencompl/riscv-lean"
for C in $RL_OLD $RL_NEW; do
  for f in RISCV/SailToRV64.lean RISCV/SailPureToInstructions.lean; do
    echo "$C $f theorem=$(show riscv-lean $C $f | grep -c '^theorem') bv_decide=$(show riscv-lean $C $f | grep -c 'bv_decide')"
  done
done
show riscv-lean $RL_OLD RISCV/SailToRV64.lean | grep -n 'theorem shiftiop_slli_eq'
show riscv-lean $RL_NEW RISCV/SailToRV64.lean | grep -n 'theorem shiftiop_slli_eq'
echo "privileged identifiers at HEAD: $(for f in $(git -C $WORK/riscv-lean ls-tree --name-only $RL_NEW RISCV/); do show riscv-lean $RL_NEW $f; done | grep -c -i -E 'mret|sret|satp|ecall|csrr|translateAddr')"

echo; echo "== opencompl/sail-riscv-lean $SRL check_CSR"
show sail-riscv-lean $SRL LeanRV64D/SysControl.lean | sed -n '526,528p'
echo "== rems-project/sail short-circuit fix $SAIL_FIX"
git -C $WORK/sail log -1 --format='%H %ad %s' $SAIL_FIX
for t in 0.20.2 0.20.3 60695b1ea377048f0adc39c62671cd099b2ed9f6; do git -C $WORK/sail merge-base --is-ancestor $SAIL_FIX $t && echo "$t contains fix" || echo "$t lacks fix"; done

echo; echo "== Miralis $MIR / softcore-rs $SC"
show miralis $MIR model_checking/src/lib.rs | grep -n -A2 'kani::proof' | grep 'pub fn' | sed 's/^/  /'
show miralis $MIR model_checking/src/model.rs | sed -n '248,250p'
show miralis $MIR model_checking/src/symbolic.rs | grep -n 'ctx.regs = \|ctx.csr.pmpcfg = \|ctx.csr.pmpaddr = '
show softcore-rs $SC justfile | sed -n '1p'
echo "softcore raw.rs todo!/unimplemented!: $(show softcore-rs $SC rv64/src/raw.rs | grep -c 'todo!\|unimplemented!')"
echo "softcore walk/translate fns: $(show softcore-rs $SC rv64/src/raw.rs | grep -c -i -E 'pub fn [a-z_]*(walk|translate)')"
show softcore-rs $SC sail_models/riscv.patch | grep -n 'is_CSR_defined(0x3A)'

echo; echo "== Serval $SERVAL"
show serval $SERVAL serval/riscv/interp/r-type.rkt | sed -n '80,82p'
show serval $SERVAL serval/riscv/interp/r-type.rkt | sed -n '84p;91p'
show serval $SERVAL serval/riscv/interp/i-type.rkt | sed -n '71p'
show serval $SERVAL serval/riscv/interp.rkt | sed -n '45p'
show serval $SERVAL test/riscv-tests/riscv-tests.mk | sed -n '2,18p' | grep -v '^$'

echo; echo "== Islaris $ISL"
show islaris $ISL theories/riscv64/sys_regs.v | sed -n '64,80p'

echo; echo "== l4v $L4V"
show l4v $L4V spec/machine/RISCV64/MachineOps.thy | sed -n '197,207p;221,223p'
show l4v $L4V spec/machine/MachineMonad.thy | grep -n -A1 'definition machine_op_lift'

echo; echo "== Ibex $IBEX proof holes"
show ibex $IBEX dv/formal/README.md | sed -n '170,190p'

echo; echo "== ACE-RISCV $ACE"
show ace $ACE verification/theories/page_table/page_table.v | sed -n '14,15p'

echo; echo "== xv6iris $XV6"
show xv6iris $XV6 lean-toolchain
show xv6iris $XV6 tools/regen_sail_model.sh | grep -n 'SAIL_RISCV_REV='
show xv6iris $XV6 tools/audit/baseline.json | grep -n -A3 '"Xv6.userProof"'
