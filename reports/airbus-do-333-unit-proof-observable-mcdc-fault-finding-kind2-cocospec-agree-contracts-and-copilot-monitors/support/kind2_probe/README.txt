Kind 2 contract probes (observed 2026-11-20, x86_64 Linux host).
Tools: kind2 v3.0.0 release binary (kind2-v3.0.0-linux-x86_64.tar.gz,
sha256 a8d08130a1ae8039ff42474fccee955880491061fc7b97d3954d3e66e6faa19d),
Z3 5.3.3 release (z3-5.3.3-x64-glibc-2.39.zip,
sha256 d56f60b06f432f33de5810f7f1a384a339131f361e2d54d08ea83eea14326880).

Commands (Z3 = path to the z3 binary):
  /usr/bin/time -v kind2 --smt_solver Z3 --z3_bin $Z3 --check_reach true --timeout 120 --color false defects.lus      > run_defects.txt      2> time_defects.txt
  /usr/bin/time -v kind2 --smt_solver Z3 --z3_bin $Z3 --modular true --compositional true --check_reach true --timeout 120 --color false defects.lus > run_defects_comp.txt 2> time_defects_comp.txt
  /usr/bin/time -v kind2 --smt_solver Z3 --z3_bin $Z3 --enable CONTRACTCK --timeout 120 --color false realiz.lus      > run_realiz.txt       2> time_realiz.txt
  kind2 --smt_solver Z3 --z3_bin $Z3 --enable CONTRACTCK --timeout 60 --color false realiz2.lus > run_realiz2.txt 2>&1
  kind2 --smt_solver Z3 --z3_bin $Z3 --timeout 60 --color false realiz2.lus     (property check of the same file; output summarized in the report)

Note: run_defects.txt was produced before the two "trivially true" guarantees were added to
SystemUnitsBug and SystemUnitsRangeVisible (that run reports those nodes as having no property);
run_defects_comp.txt was produced with the defects.lus preserved here.
