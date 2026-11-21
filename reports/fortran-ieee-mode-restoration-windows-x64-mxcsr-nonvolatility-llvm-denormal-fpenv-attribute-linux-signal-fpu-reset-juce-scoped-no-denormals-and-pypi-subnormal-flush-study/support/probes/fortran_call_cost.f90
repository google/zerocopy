! Probe: per-call cost of gfortran's IEEE procedure entry/exit save/restore.
module k
contains
  subroutine plain(x)
    real(8), intent(inout) :: x
    !GCC$ ATTRIBUTES noinline :: plain
    x = x * 1.0000001d0
  end subroutine
  subroutine with_ieee(x)
    use, intrinsic :: ieee_arithmetic, only: ieee_support_datatype
    real(8), intent(inout) :: x
    !GCC$ ATTRIBUTES noinline :: with_ieee
    x = x * 1.0000001d0
  end subroutine
end module
program bench
  use k
  implicit none
  integer(8) :: i, n, c0, c1, rate
  integer :: r
  real(8) :: x, t(7), tp(7), tmp
  n = 20000000_8
  do r = 1, 7
    x = 1d0
    call system_clock(c0, rate); do i = 1, n; call plain(x); end do; call system_clock(c1)
    tp(r) = dble(c1 - c0) / dble(rate) / dble(n) * 1d9
    x = 1d0
    call system_clock(c0, rate); do i = 1, n; call with_ieee(x); end do; call system_clock(c1)
    t(r) = dble(c1 - c0) / dble(rate) / dble(n) * 1d9
  end do
  call sort(tp); call sort(t)
  print '(a,f8.2,a,f8.2,a,g12.4)', 'median ns/call: plain=', tp(4), '  ieee-module-using=', t(4), '  x=', x
contains
  subroutine sort(a)
    real(8), intent(inout) :: a(:)
    integer :: p, q
    do p = 1, size(a); do q = p + 1, size(a)
      if (a(q) < a(p)) then; tmp = a(p); a(p) = a(q); a(q) = tmp; end if
    end do; end do
  end subroutine
end program
