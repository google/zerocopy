#!/usr/bin/env python3
"""Single GeneralizedCentrifugalForceModel agent in the bottleneck geometry of jps_probe.py;
prints position and speed every 1 s. Args: x0 y0 dt."""
import sys
import pyjupedsim as jps
from jps_probe import ROOM, EXIT
x0, y0, dt = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
gb = jps.GeometryBuilder(); region = gb.add_region(boundary=ROOM, height=0.0); geo = gb.build()
sim = jps._Simulation(model=jps.GeneralizedCentrifugalForceModel(), geometry=geo, dt=dt,
                      floorfield_options=jps.FloorfieldOptions())
ex = sim.add_exit_stage([(EXIT, region)])
j = sim.add_journey({ex: jps.Transition.create_none_transition()})
aid = sim.add_agent(journey_id=j, stage_id=ex, position=(x0, y0),
                    state=jps.GeneralizedCentrifugalForceModelState(desired_speed=1.2), region_id=region)
while sim.elapsed_time() < 120 and sim.agent_count() > 0:
    sim.iterate()
    if abs(sim.elapsed_time() % 1.0) < dt / 2 or abs(sim.elapsed_time() % 1.0 - 1.0) < dt / 2:
        a = sim.agent(aid); s = a.state
        print(f"t={sim.elapsed_time():6.2f} pos=({a.position[0]:.3f},{a.position[1]:.3f}) speed={s.speed:.3f} orient={s.orientation}")
print("exited" if sim.agent_count() == 0 else "not exited", f"t={sim.elapsed_time():.2f}")
