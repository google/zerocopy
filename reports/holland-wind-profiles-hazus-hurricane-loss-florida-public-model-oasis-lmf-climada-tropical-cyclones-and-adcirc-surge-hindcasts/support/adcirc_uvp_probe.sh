#!/bin/sh
# Compile ADCIRC vortex.F lines 704-709 (the speedAtRmax expression in subroutine uvp)
# verbatim as fixed-form Fortran and print the value, to show how gfortran parses the
# "*" that ends line 705 followed by the "*" that starts continuation line 706.
# Subject: adcirc/adcirc@ae33c51ffc2922f33dbf042e2948701c22e7bdc3, wind/vortex.F.
# Usage: sh adcirc_uvp_probe.sh /tmp/scratchdir
set -e
W="$1"; mkdir -p "$W"; cd "$W"
SHA=ae33c51ffc2922f33dbf042e2948701c22e7bdc3
curl -sSL -H "User-Agent: research-bot" \
  "https://raw.githubusercontent.com/adcirc/adcirc/$SHA/wind/vortex.F" -o vortex.F
sed -n '704,709p' vortex.F > expr.inc
grep -q 'speedAtRmax = SQRT' expr.inc || { echo "line range moved"; exit 3; }
cat expr.inc
{
  printf '      PROGRAM P\n'
  printf '      IMPLICIT NONE\n'
  printf '      REAL(8) Vmax,kt2ms,nm2m,dist,percentCoriolis,corio,speedAtRmax\n'
  printf '      REAL(8) expect_mul, expect_naive\n'
  printf '      Vmax=100.d0\n      kt2ms=1852.d0/3600.d0\n      nm2m=1852.d0\n'
  printf '      dist=150.d0\n      percentCoriolis=1.d0\n      corio=6.16d-5\n'
  cat expr.inc
  printf '      expect_naive = SQRT((Vmax*kt2ms)**2+(nm2m*dist*corio/2)**2)\n'
  printf '     &   - nm2m*dist*corio/2\n'
  printf "      PRINT '(A,F12.6)', 'speedAtRmax (compiled) = ', speedAtRmax\n"
  printf "      PRINT '(A,F12.6)', 'sqrt(V^2+c^2)-c        = ', expect_naive\n"
  printf '      END\n'
} > p.F
gfortran -ffixed-line-length-132 -o p p.F
./p
