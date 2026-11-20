#!/usr/bin/env python3
"""Bottleneck-evacuation probe of JuPedSim operational models (raw pyjupedsim bindings).

Geometry ("base"): 8 m x 8 m room (x in [0,8], y in [0,8]) with a 1.0 m wide, 2.0 m long exit
corridor attached at x = 8, y in [3.5, 4.5]; the exit stage is the last 0.5 m of the
corridor (x in [9.5, 10]).  N agents start on a jittered grid in x in [1, 5.5].

Per run it records: simulated evacuation time, minimum centre-centre distance between any
two agents over the run, maximum circular overlap (r_i + r_j - d_ij) for circular models,
the fraction of agent-steps whose displacement points away from the exit centre
("backward" steps; a crude oscillation indicator), any SimulationError, wall-clock time
and number of agent-iterations.

Usage: jps_probe.py <json-config> ; prints one JSON line.
"""
import json
import math
import random
import sys
import time

import numpy as np
import pyjupedsim as jps

ROOM = [(0, 0), (8, 0), (8, 3.5), (10, 3.5), (10, 4.5), (8, 4.5), (8, 8), (0, 8)]
EXIT = [(9.5, 3.5), (10, 3.5), (10, 4.5), (9.5, 4.5)]
# "ext" variant: the corridor continues to x = 14 so that no wall lies directly behind the exit
# stage (relevant for models with long-range wall repulsion such as GCFM).
ROOM_EXT = [(0, 0), (8, 0), (8, 3.5), (14, 3.5), (14, 4.5), (8, 4.5), (8, 8), (0, 8)]
EXIT_CENTRE = np.array([9.75, 4.0])
DOOR_CENTRE = np.array([8.0, 4.0])


def positions(n, seed, spacing=0.75):
    rng = random.Random(seed)
    pts = []
    x = 1.0
    while len(pts) < n:
        y = 0.9
        while y <= 7.1 and len(pts) < n:
            pts.append((x + rng.uniform(-0.1, 0.1), y + rng.uniform(-0.1, 0.1)))
            y += spacing
        x += spacing
    return pts


def make(model_name, params):
    v0 = params.get("v0", 1.2)
    if model_name == "SFM":
        model = jps.SocialForceModel(body_force=params.get("body_force", 120000),
                                     friction=params.get("friction", 240000))
        def state():
            return jps.SocialForceModelState(
                desired_speed=v0,
                reaction_time=params.get("reaction_time", 0.5),
                agent_scale=params.get("agent_scale", 2000.0),
                obstacle_scale=params.get("obstacle_scale", 2000.0),
                force_distance=params.get("force_distance", 0.08),
                radius=params.get("radius", 0.3),
                mass=params.get("mass", 80.0))
        radius = params.get("radius", 0.3)
    elif model_name == "GCFM":
        model = jps.GeneralizedCentrifugalForceModel(
            strength_neighbor_repulsion=params.get("strength_neighbor_repulsion", 0.3),
            strength_wall_repulsion=params.get("strength_wall_repulsion", 0.2))
        def state():
            return jps.GeneralizedCentrifugalForceModelState(
                desired_speed=v0, tau=params.get("tau", 0.5))
        radius = None
    elif model_name == "CFSM":
        model = jps.CollisionFreeSpeedModel(
            strength_neighbor_repulsion=params.get("strength_neighbor_repulsion", 8.0),
            range_neighbor_repulsion=params.get("range_neighbor_repulsion", 0.1))
        def state():
            return jps.CollisionFreeSpeedModelState(
                desired_speed=v0, time_gap=params.get("time_gap", 1.0),
                radius=params.get("radius", 0.2))
        radius = params.get("radius", 0.2)
    elif model_name == "AVM":
        model = jps.AnticipationVelocityModel(rng_seed=params.get("rng_seed", 42))
        def state():
            return jps.AnticipationVelocityModelState(
                desired_speed=v0, time_gap=params.get("time_gap", 1.06),
                anticipation_time=params.get("anticipation_time", 1.0),
                reaction_time=params.get("reaction_time", 0.3),
                radius=params.get("radius", 0.2))
        radius = params.get("radius", 0.2)
    else:
        raise ValueError(model_name)
    return model, state, radius


def run(cfg):
    model_name = cfg["model"]
    dt = cfg["dt"]
    n = cfg.get("n", 60)
    tmax = cfg.get("tmax", 300.0)
    model, state, radius = make(model_name, cfg.get("params", {}))
    gb = jps.GeometryBuilder()
    region = gb.add_region(boundary=ROOM_EXT if cfg.get("geometry") == "ext" else ROOM, height=0.0)
    geo = gb.build()
    sim = jps._Simulation(model=model, geometry=geo, dt=dt,
                          floorfield_options=jps.FloorfieldOptions())
    exit_id = sim.add_exit_stage([(EXIT, region)])
    journey = sim.add_journey({exit_id: jps.Transition.create_none_transition()})
    for p in positions(n, cfg.get("seed", 0)):
        sim.add_agent(journey_id=journey, stage_id=exit_id, position=p, state=state(),
                      region_id=region)
    out = dict(cfg)
    min_d = math.inf
    max_overlap = 0.0
    overlap_pair_frames = 0
    pair_frames = 0
    back = 0
    steps = 0
    agent_iters = 0
    prev = {}
    err = None
    exit_times = []
    t0 = time.perf_counter()
    try:
        while sim.agent_count() > 0 and sim.elapsed_time() < tmax:
            before = sim.agent_count()
            sim.iterate()
            exit_times += [sim.elapsed_time()] * (before - sim.agent_count())
            agents = list(sim.agents())
            agent_iters += len(agents)
            if not agents:
                break
            ids = [a.id for a in agents]
            pos = np.array([a.position for a in agents], dtype=float)
            # backward-step indicator relative to door (inside room) or exit (corridor)
            for i, aid in enumerate(ids):
                if aid in prev:
                    move = pos[i] - prev[aid]
                    target = DOOR_CENTRE if pos[i][0] < 8.0 else EXIT_CENTRE
                    to_t = target - prev[aid]
                    nrm = np.linalg.norm(to_t)
                    if nrm > 1e-9 and np.linalg.norm(move) > 1e-9:
                        steps += 1
                        if np.dot(move, to_t) / nrm < -1e-9:
                            back += 1
            prev = {aid: pos[i] for i, aid in enumerate(ids)}
            if len(pos) > 1:
                d = np.sqrt(((pos[:, None, :] - pos[None, :, :]) ** 2).sum(-1))
                iu = np.triu_indices(len(pos), 1)
                dd = d[iu]
                min_d = min(min_d, float(dd.min()))
                pair_frames += dd.size
                if radius is not None:
                    ov = 2 * radius - dd
                    max_overlap = max(max_overlap, float(ov.max()))
                    overlap_pair_frames += int((ov > 1e-9).sum())
    except Exception as e:  # SimulationError from libsimulator
        err = f"{type(e).__name__}: {e}"
    wall = time.perf_counter() - t0
    def tq(q):
        k = int(math.ceil(q * n))
        return exit_times[k - 1] if len(exit_times) >= k else None
    out.update(
        t50=tq(0.5), t90=tq(0.9),
        remaining_positions=[tuple(round(c, 3) for c in a.position) for a in sim.agents()][:5],
        evac_time=sim.elapsed_time() if sim.agent_count() == 0 else None,
        remaining=sim.agent_count(),
        sim_time=sim.elapsed_time(),
        min_center_distance=None if min_d == math.inf else min_d,
        max_overlap=max_overlap if radius is not None else None,
        overlap_fraction=(overlap_pair_frames / pair_frames) if (radius is not None and pair_frames) else None,
        backward_step_fraction=(back / steps) if steps else None,
        error=err,
        wall_s=wall,
        agent_iterations=agent_iters,
    )
    return out


if __name__ == "__main__":
    print(json.dumps(run(json.loads(sys.argv[1]))), flush=True)
