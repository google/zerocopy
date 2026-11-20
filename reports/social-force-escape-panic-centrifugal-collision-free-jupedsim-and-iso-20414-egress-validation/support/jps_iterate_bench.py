#!/usr/bin/env python3
"""Engine-only timing: 60 agents in the jps_probe.py bottleneck geometry, time 500 calls of
iterate() (dt = 0.01 s) with no Python-side metric collection. Prints us per agent-iteration."""
import time
import pyjupedsim as jps
from jps_probe import ROOM, EXIT, positions, make
for m in ["SFM", "GCFM", "CFSM", "AVM"]:
    model, state, _ = make(m, {})
    gb = jps.GeometryBuilder(); region = gb.add_region(boundary=ROOM, height=0.0); geo = gb.build()
    sim = jps._Simulation(model=model, geometry=geo, dt=0.01, floorfield_options=jps.FloorfieldOptions())
    ex = sim.add_exit_stage([(EXIT, region)])
    j = sim.add_journey({ex: jps.Transition.create_none_transition()})
    for p in positions(60, 0):
        sim.add_agent(journey_id=j, stage_id=ex, position=p, state=state(), region_id=region)
    n0 = sim.agent_count(); t0 = time.perf_counter(); ai = 0
    try:
        for _ in range(500):
            ai += sim.agent_count(); sim.iterate()
    except Exception as e:
        print(m, "error", e)
    dtw = time.perf_counter() - t0
    print(f"{m}: {ai} agent-iterations in {dtw:.3f} s -> {1e6*dtw/ai:.1f} us/agent-iteration (agents start {n0}, end {sim.agent_count()})")
