#!/usr/bin/env python3
"""Single-agent SocialForceModel probe in the bottleneck geometry of jps_probe.py.
Args: x0 y0 dt desired_speed obstacle_scale.
Logs position and velocity of one agent starting at (x0, 4.0) walking towards the exit."""
import sys
import pyjupedsim as jps
from jps_probe import ROOM, EXIT
x0 = float(sys.argv[1]) if len(sys.argv) > 1 else 6.0
y0 = float(sys.argv[2]) if len(sys.argv) > 2 else 4.0
dt = float(sys.argv[3]) if len(sys.argv) > 3 else 0.01
gb = jps.GeometryBuilder(); region = gb.add_region(boundary=ROOM, height=0.0); geo = gb.build()
sim = jps._Simulation(model=jps.SocialForceModel(body_force=120000, friction=240000), geometry=geo, dt=dt,
                      floorfield_options=jps.FloorfieldOptions())
ex = sim.add_exit_stage([(EXIT, region)])
j = sim.add_journey({ex: jps.Transition.create_none_transition()})
aid = sim.add_agent(journey_id=j, stage_id=ex, position=(x0, y0),
                    state=jps.SocialForceModelState(desired_speed=float(sys.argv[4]) if len(sys.argv) > 4 else 1.2, mass=80.0, radius=0.3, obstacle_scale=float(sys.argv[5]) if len(sys.argv) > 5 else 2000.0), region_id=region)
for k in range(int(30 / dt)):
    sim.iterate()
    if sim.agent_count() == 0:
        print(f"exited at t={sim.elapsed_time():.2f}s"); break
    if k % int(0.5 / dt) == 0:
        a = sim.agent(aid)
        print(f"t={sim.elapsed_time():6.2f} pos=({a.position[0]:.4f},{a.position[1]:.4f}) v={a.state.velocity}")
else:
    a = sim.agent(aid); print(f"NOT EXITED after 30 s; final pos={a.position} v={a.state.velocity}")
