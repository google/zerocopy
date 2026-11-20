#!/usr/bin/env python3
"""Suspicion-of-infection window probe (standard library only).

This is a TRANSCRIPTION of the time-window join predicates found in two
versions of the open MIMIC cohort-derivation SQL (MIT-LCP/mimic-code at
revision 303d26c623dcc9c49cc0f204468d4acc2f063797):

  * mimic-iv/concepts/sepsis/suspicion_of_infection.sql
      culture-then-antibiotic branch (lines 82-89, charttime present):
          abx_time >  culture_time  AND abx_time <= culture_time + 72 h
      antibiotic-then-culture branch (lines 137-142, charttime present):
          abx_time >= culture_time - 24 h AND abx_time < culture_time
      suspected_infection_time (lines 169-173):
          COALESCE(earliest culture in the 72 h branch, antibiotic_time)
  * mimic-iii/concepts/treatment/suspicion_of_infection.sql
      72 h branch (lines 57-60):  abx_time >= culture_time AND abx_time <= culture_time + 72 h
      24 h branch (lines 76-79):  abx_time <= culture_time AND abx_time >= culture_time - 24 h
      suspected_infection_time (line 104):
          COALESCE(last72_charttime, next24_charttime)   -- a culture time in both branches

The predicates are evaluated by SQLite on synthetic single-patient inputs.
This is NOT an execution of the upstream SQL (which targets BigQuery /
PostgreSQL / DuckDB dialects and MIMIC tables); it checks the boundary
semantics of the transcribed predicates only.
"""
import sqlite3
import time

t0 = time.perf_counter()
con = sqlite3.connect(":memory:")
# Offsets are culture_time - antibiotic_time, in hours.
offsets = [-73, -72, -71, -24.5, -24, -1, -0.5, 0, 0.5, 1, 23.5, 24, 24.5]
con.execute("CREATE TABLE ev(off REAL)")
con.executemany("INSERT INTO ev VALUES (?)", [(o,) for o in offsets])

# Antibiotic at t = 0 h; culture at t = off h. Work in hours as REAL.
q = """
SELECT off,
  -- MIMIC-IV culture-then-antibiotic (strict >, inclusive <= 72)
  CASE WHEN 0 > off AND 0 <= off + 72 THEN 1 ELSE 0 END AS iv_me_then_ab,
  -- MIMIC-IV antibiotic-then-culture (inclusive >= -24, strict <)
  CASE WHEN 0 >= off - 24 AND 0 < off THEN 1 ELSE 0 END AS iv_ab_then_me,
  -- MIMIC-III 72 h branch (inclusive both ends)
  CASE WHEN 0 >= off AND 0 <= off + 72 THEN 1 ELSE 0 END AS iii_72,
  -- MIMIC-III 24 h branch (inclusive both ends)
  CASE WHEN 0 <= off AND 0 >= off - 24 THEN 1 ELSE 0 END AS iii_24
FROM ev ORDER BY off
"""
rows = con.execute(q).fetchall()
print("culture_minus_abx_h | IV:me->ab IV:ab->me | IV suspected? IV SI_time | III:72 III:24 | III suspected? III SI_time")
for off, a, b, c, d in rows:
    iv_s = a or b
    # MIMIC-IV SI time: culture time if culture-first branch matched, else antibiotic time (0)
    iv_si = (off if a else 0.0) if iv_s else None
    iii_s = c or d
    # MIMIC-III SI time: COALESCE(last72_charttime, next24_charttime) -> culture time either way
    iii_si = off if iii_s else None
    print(f"{off:>8} | {a} {b} | {iv_s} {iv_si} | {c} {d} | {iii_s} {iii_si}")

# SOFA window used by mimic-iv/concepts/sepsis/sepsis3.sql lines 57-62:
#   sofa.endtime >= SI - 48 h AND sofa.endtime <= SI + 24 h  (inclusive both ends)
print()
print("sepsis3.sql SOFA window membership for SOFA endtime offsets relative to SI time:")
for e in [-48.5, -48, 0, 24, 24.5]:
    inside = (e >= -48) and (e <= 24)
    print(f"  endtime - SI = {e:>6} h -> {'inside' if inside else 'outside'}")
print(f"elapsed_s={time.perf_counter() - t0:.4f}")
