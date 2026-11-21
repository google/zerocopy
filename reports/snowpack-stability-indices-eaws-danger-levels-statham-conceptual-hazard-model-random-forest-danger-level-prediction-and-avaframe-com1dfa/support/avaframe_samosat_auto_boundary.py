"""Probe the samosATAuto volume-class boundary in AvaFrame com1DFA.

Calls avaframe.com1DFA.checkCfg.checkCfgFrictionModel with the default com1DFA
configuration and release volumes around the configured class limits
(volClassSmall = 25000, volClassMedium = 60000 m^3), and also calls
com1DFA.setVolumeIndicator for the same volumes.  Prints the friction model that
results and whether it is one that DFAIterate's frictModelsList can index.
Requires an installed avaframe (tested at OpenNHM/AvaFrame@61f1bb9).
"""
import configparser
import logging

logging.disable(logging.CRITICAL)

from avaframe.in3Utils import cfgUtils
import avaframe.com1DFA.com1DFA as com1DFA
import avaframe.com1DFA.checkCfg as checkCfg

FRICT_MODELS = ["samosat", "coulomb", "voellmy", "wetsnow", "samosatsmall", "samosatmedium",
                "voellmyminshear", "coulombminshear", "spatialvoellmy", "obrienandjulien",
                "herschelandbulkley", "bingham"]  # copied from com1DFA.py DFAIterate

for vol in (24999.0, 25000.0, 59999.0, 60000.0, 60001.0):
    cfg = cfgUtils.getModuleConfig(com1DFA, toPrint=False)
    cfg["GENERAL"]["frictModel"] = "samosATAuto"
    sim = configparser.ConfigParser()
    sim.read_dict({s: dict(cfg[s]) for s in cfg.sections()})
    try:
        out = checkCfg.checkCfgFrictionModel(sim, {}, relVolume=vol)
        fm = out["GENERAL"]["frictModel"]
    except Exception as e:  # report rather than hide
        fm = "EXCEPTION " + repr(e)
    indi = com1DFA.setVolumeIndicator(sim, vol)
    print(f"relVolume={vol:>8.0f}  frictModel -> {fm:<14} indexable={fm.lower() in FRICT_MODELS}  volumeIndicator={indi}")
