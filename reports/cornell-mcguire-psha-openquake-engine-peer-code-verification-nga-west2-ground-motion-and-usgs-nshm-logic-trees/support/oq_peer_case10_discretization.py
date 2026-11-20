"""Sensitivity of OpenQuake's encoding of PEER 2010/106 Set 1 Case 10 (area source,
single 5 km depth, sigma = 0 via truncation_level = 0) to the area discretization,
measured against the benchmark PoEs stored by the acceptance test itself
(openquake/hazardlib/tests/acceptance/_peer_test_data.py).

Everything except `area_discretization` (and rupture_mesh_spacing, kept equal) is
copied from peer_test.py::Set1TestCase.test_case_10 at the pinned revision.
Usage: python oq_peer_case10_discretization.py <oq-engine source root> [10,5,2,1]
"""
import sys
import time

import numpy

sys.path.insert(0, sys.argv[1])
from openquake.hazardlib import const  # noqa: E402
from openquake.hazardlib.site import SiteCollection  # noqa: E402
from openquake.hazardlib.source import AreaSource  # noqa: E402
from openquake.hazardlib.pmf import PMF  # noqa: E402
from openquake.hazardlib.geo import NodalPlane  # noqa: E402
from openquake.hazardlib.scalerel import PointMSR  # noqa: E402
from openquake.hazardlib.gsim.sadigh_1997 import SadighEtAl1997  # noqa: E402
from openquake.hazardlib.calc.hazard_curve import calc_hazard_curves  # noqa: E402
from openquake.hazardlib.tom import PoissonTOM  # noqa: E402
from openquake.hazardlib.tests.acceptance import _peer_test_data as td  # noqa: E402

expected = [numpy.array(e) for e in (td.SET1_CASE10_SITE1_POES, td.SET1_CASE10_SITE2_POES,
                                     td.SET1_CASE10_SITE3_POES, td.SET1_CASE10_SITE4_POES)]


def run(disc):
    src = AreaSource(
        source_id='area', name='area',
        tectonic_region_type=const.TRT.ACTIVE_SHALLOW_CRUST,
        mfd=td.SET1_CASE10_MFD,
        nodal_plane_distribution=PMF([(1, NodalPlane(0.0, 90.0, 0.0))]),
        hypocenter_distribution=PMF([(1, td.SET1_CASE10_HYPOCENTER_DEPTH)]),
        upper_seismogenic_depth=0.0, lower_seismogenic_depth=10.0,
        magnitude_scaling_relationship=PointMSR(),
        rupture_aspect_ratio=td.SET1_RUPTURE_ASPECT_RATIO,
        temporal_occurrence_model=PoissonTOM(1.),
        polygon=td.SET1_CASE10_SOURCE_POLYGON,
        area_discretization=disc, rupture_mesh_spacing=disc)
    sites = SiteCollection([td.SET1_CASE10_SITE1, td.SET1_CASE10_SITE2,
                            td.SET1_CASE10_SITE3, td.SET1_CASE10_SITE4])
    imts = {str(td.IMT): td.SET1_CASE10_IMLS}
    t0 = time.perf_counter()
    curves = calc_hazard_curves([src], sites, imts,
                                {const.TRT.ACTIVE_SHALLOW_CRUST: SadighEtAl1997()}, 0)
    return curves[str(td.IMT)], time.perf_counter() - t0, src.count_ruptures()


def maxrel(got, floor):
    worst, where = 0.0, None
    imls = numpy.array(td.SET1_CASE10_IMLS)
    for s in range(4):
        m = expected[s] >= floor
        if not m.any():
            continue
        rel = numpy.abs(got[s][m] / expected[s][m] - 1)
        if rel.max() > worst:
            worst = float(rel.max())
            where = f"site{s + 1}/IML={imls[m][rel.argmax()]}"
    return worst, where


discs = [float(x) for x in (sys.argv[2] if len(sys.argv) > 2 else "10,5,2,1").split(",")]
print("disc_km ruptures secs | lowest-IML rel.err (site1) | max rel.err PoE>=1e-4 [where] | "
      "max rel.err PoE>=1e-5 [where] | passes encoded tol | all PoE>=1e-5 within 5%")
for disc in discs:
    got, dt, nrup = run(disc)
    got = numpy.asarray(got)
    lo = got[0][0] / expected[0][0] - 1
    w4, at4 = maxrel(got, 1e-4)
    w5, at5 = maxrel(got, 1e-5)
    ok = all(numpy.allclose(got[s], expected[s], atol=1e-4, rtol=1e-1) for s in range(4))
    print(f"{disc:6.1f} {nrup:8d} {dt:7.2f} | {lo:+.3%} | {w4:.3%} [{at4}] | {w5:.3%} [{at5}] | "
          f"{ok} | {w5 <= 0.05}", flush=True)
