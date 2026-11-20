#!/usr/bin/env python3
"""Single SocialForceModel agent approaching a door; door geometry variants.
Args: variant(corridor|thinwall) door_width desired_speed [obstacle_scale] [dt].
corridor: 8x8 room, door of given width centred at y=4 on x=8, followed by a 2 m corridor.
thinwall: two 8 m deep rooms separated by a 0.2 m thick wall with a door of given width."""
import sys
import pyjupedsim as jps
variant, w, v0 = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
A = float(sys.argv[4]) if len(sys.argv) > 4 else 2000.0
dt = float(sys.argv[5]) if len(sys.argv) > 5 else 0.01
lo, hi = 4.0 - w / 2, 4.0 + w / 2
if variant == "corridor":
    poly = [(0, 0), (8, 0), (8, lo), (10, lo), (10, hi), (8, hi), (8, 8), (0, 8)]
    exit_area = [(9.5, lo), (10, lo), (10, hi), (9.5, hi)]
else:
    poly = [(0, 0), (8, 0), (8, lo), (8.2, lo), (8.2, 0), (16, 0), (16, 8), (8.2, 8), (8.2, hi), (8, hi), (8, 8), (0, 8)]
    exit_area = [(15, 3), (16, 3), (16, 5), (15, 5)]
gb = jps.GeometryBuilder(); region = gb.add_region(boundary=poly, height=0.0); geo = gb.build()
sim = jps._Simulation(model=jps.SocialForceModel(body_force=120000, friction=240000), geometry=geo, dt=dt,
                      floorfield_options=jps.FloorfieldOptions())
ex = sim.add_exit_stage([(exit_area, region)])
j = sim.add_journey({ex: jps.Transition.create_none_transition()})
aid = sim.add_agent(journey_id=j, stage_id=ex, position=(6.0, 4.0),
                    state=jps.SocialForceModelState(desired_speed=v0, mass=80.0, radius=0.3, obstacle_scale=A),
                    region_id=region)
while sim.elapsed_time() < 40 and sim.agent_count() > 0:
    sim.iterate()
    if sim.agent_count() and sim.agent(aid).position[0] > 8.2:
        print(f"{variant} w={w} v0={v0} A={A} dt={dt}: PASSED door at t={sim.elapsed_time():.2f}s"); break
else:
    a = sim.agent(aid)
    print(f"{variant} w={w} v0={v0} A={A} dt={dt}: STOPPED, final x={a.position[0]:.4f} y={a.position[1]:.4f} |v|={(a.state.velocity[0]**2+a.state.velocity[1]**2)**0.5:.2e}")
