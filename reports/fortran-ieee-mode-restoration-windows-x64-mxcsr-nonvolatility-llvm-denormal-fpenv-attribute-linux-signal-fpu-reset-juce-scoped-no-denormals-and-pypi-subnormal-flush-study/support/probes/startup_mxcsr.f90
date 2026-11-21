program s
  use, intrinsic :: ieee_arithmetic
  print '(a,l1)', 'IEEE_GET_UNDERFLOW_MODE gradual = ', get_gradual()
contains
  logical function get_gradual()
    call ieee_get_underflow_mode(get_gradual)
  end function
end program
