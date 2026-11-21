! Probe: Fortran IEEE mode/flag rules on procedure entry/return, and what
! happens when the mode is changed by a C function (bind(C)).
module m
  use, intrinsic :: iso_c_binding
  interface
    subroutine c_set_downward() bind(C, name="c_set_downward")
    end subroutine
    integer(c_int) function c_get_round() bind(C, name="c_get_round")
      import :: c_int
    end function
  end interface
contains
  subroutine ieee_sets_down()          ! uses IEEE_ARITHMETIC: processor must restore on return
    use, intrinsic :: ieee_arithmetic
    call ieee_set_rounding_mode(ieee_down)
  end subroutine
  subroutine plain_calls_c()           ! does not use the IEEE modules
    call c_set_downward()
  end subroutine
  subroutine ieee_calls_c()            ! uses IEEE modules, mode changed by C callee
    use, intrinsic :: ieee_arithmetic
    logical :: f
    call ieee_get_flag(ieee_overflow, f)   ! any reference makes the procedure "use" the module
    call c_set_downward()
  end subroutine
  subroutine ieee_raises_overflow(x)
    use, intrinsic :: ieee_exceptions
    real(8), intent(inout) :: x
    logical :: f
    call ieee_get_flag(ieee_overflow, f)
    print '(a,l1)', '  callee sees OVERFLOW flag on entry = ', f
    x = x * x
  end subroutine
end module
program p
  use m
  use, intrinsic :: ieee_arithmetic
  type(ieee_round_type) :: r
  logical :: f
  real(8) :: big
  call ieee_get_rounding_mode(r); print '(a,l1)', 'start nearest? ', r == ieee_nearest
  call ieee_sets_down();  call ieee_get_rounding_mode(r); print '(a,l1)', 'after IEEE-using callee set DOWN, caller nearest? ', r == ieee_nearest
  call plain_calls_c();   print '(a,i0)', 'after non-IEEE Fortran callee -> C fesetround(FE_DOWNWARD): C fegetround()=', c_get_round()
  call ieee_set_rounding_mode(ieee_nearest)
  call ieee_calls_c();    print '(a,i0)', 'after IEEE-using Fortran callee -> C fesetround(FE_DOWNWARD): C fegetround()=', c_get_round()
  call ieee_set_flag(ieee_overflow, .false.)
  big = 1.0d300; call ieee_raises_overflow(big)
  call ieee_get_flag(ieee_overflow, f); print '(a,l1)', 'caller OVERFLOW flag after callee overflowed = ', f
  call ieee_set_flag(ieee_overflow, .true.)
  big = 1.0d0; call ieee_raises_overflow(big)
  call ieee_get_flag(ieee_overflow, f); print '(a,l1)', 'caller OVERFLOW flag restored after quiet callee = ', f
end program
