"""Run AvaFrame's similarity-solution post-processing and dump the error table.

Mirrors avaframe/runScripts/runAnalyzeSimilaritySol.py (same calls to
simiSolTest.mainSimilaritySol and simiSolTest.postProcessSimiSol) but writes
the resulting per-simulation table to CSV instead of plotting.
Run from the `avaframe/` package directory of the source tree after
runScripts/runSimilaritySol.py has produced the simulations.
"""
import pathlib
import sys

import avaframe.in3Utils.fileHandlerUtils as fU
from avaframe.in3Utils import cfgUtils
from avaframe.in3Utils import logUtils
import avaframe.com1DFA.com1DFA as com1DFA
import avaframe.ana1Tests.simiSolTest as simiSolTest

avalancheDir = 'data/avaSimilaritySol'
cfgMain = cfgUtils.getGeneralConfig()
log = logUtils.initiateLogger(avalancheDir, 'analyzeSimiSolCSV')
simiSolCfg = pathlib.Path(avalancheDir, 'Inputs', 'simiSol_com1DFACfg.ini')
cfg = cfgUtils.getModuleConfig(com1DFA, fileOverride=simiSolCfg)
outDirTest = pathlib.Path(avalancheDir, 'Outputs', 'ana1Tests')
fU.makeADir(outDirTest)
simDF, _ = cfgUtils.readAllConfigurationInfo(avalancheDir)
solSimi = simiSolTest.mainSimilaritySol(simiSolCfg)
simDF = simiSolTest.postProcessSimiSol(avalancheDir, cfgMain, cfg, simDF, solSimi, outDirTest)
cols = [c for c in simDF.columns if c in (
    'sphKernelRadius', 'aPPK', 'nPPK0', 'nPart', 'hErrorL2', 'vhErrorL2', 'hErrorLMax', 'vhErrorLMax',
    'timeLoop', 'timeForce', 'timeForceSPH', 'timePos', 'timeNeigh', 'timeField', 'nIter')]
out = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else outDirTest / 'simiSolErrors.csv'
simDF[cols].sort_values(['sphKernelRadius', 'nPPK0', 'aPPK']).to_csv(out, index=False)
print(simDF[cols].sort_values(['sphKernelRadius', 'nPPK0', 'aPPK']).to_string())
