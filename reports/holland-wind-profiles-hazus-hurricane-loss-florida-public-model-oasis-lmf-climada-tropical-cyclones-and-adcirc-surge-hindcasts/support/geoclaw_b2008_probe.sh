#!/bin/sh
# Compile and evaluate GeoClaw's get_holland_b_2008 exactly as written at
# clawpack/geoclaw@091b28d19ecb1fb0e3b4f1881ccf4ce17d3886a8
# (src/2d/shallow/surge/parametric_met_forcing_module.f90, lines 591-602).
# The function body is extracted verbatim at run time (not stored here).
# Usage: sh geoclaw_b2008_probe.sh /tmp/scratchdir
set -e
W="$1"; mkdir -p "$W"; cd "$W"
SHA=091b28d19ecb1fb0e3b4f1881ccf4ce17d3886a8
F=parametric_met_forcing_module.f90
curl -sSL -H "User-Agent: research-bot" \
  "https://raw.githubusercontent.com/clawpack/geoclaw/$SHA/src/2d/shallow/surge/$F" -o "$F"
sed -n '591,602p' "$F" > body.f90
head -1 body.f90 | grep -q 'pure function get_holland_b_2008' || { echo "line range moved"; exit 3; }
{ echo "module b08"; echo "implicit none"; echo "contains"; cat body.f90; echo "end module b08"; } > b08.f90
cat > drv.f90 <<'EOF'
program drv
  use b08
  implicit none
  real(kind=8) :: tv(2), dp_hpa, dpdt_hpa_h, lat
  real(kind=8) :: dp_pa, dpdt_pa_s
  integer :: k
  real(kind=8) :: dps(4) = [20.d0, 50.d0, 80.d0, 100.d0]
  lat = 25.d0
  print '(a)', ' dp_hPa  vt_m/s   B(dp in hPa, dpdt hPa/h)   B(dp in Pa, dpdt Pa/s as passed by set_holland_2008_fields)'
  do k = 1, 4
    dp_hpa = dps(k); dpdt_hpa_h = 0.d0
    dp_pa = dp_hpa * 100.d0; dpdt_pa_s = dpdt_hpa_h * 100.d0 / 3600.d0
    tv = [5.d0, 0.d0]
    print '(f7.1,f8.2,2f22.5)', dp_hpa, 5.d0, get_holland_b_2008(dp_hpa, dpdt_hpa_h, lat, tv), &
                                get_holland_b_2008(dp_pa, dpdt_pa_s, lat, tv)
    tv = [0.d0, 0.d0]
    print '(f7.1,f8.2,2f22.5)', dp_hpa, 0.d0, get_holland_b_2008(dp_hpa, dpdt_hpa_h, lat, tv), &
                                get_holland_b_2008(dp_pa, dpdt_pa_s, lat, tv)
  end do
end program drv
EOF
gfortran -O0 -o drv b08.f90 drv.f90
./drv
sha256sum "$F" | awk '{print "sha256(" $2 ")=" $1}'
