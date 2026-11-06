; Copyright 2026 The Fuchsia Authors
;
; Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
; <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
; license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
; This file may not be copied, modified, or distributed except according to
; those terms.

define i128 @add_u128_and_u8(i128 %a, i128 %b, i8 %c, i8 %d) nounwind {
entry:
  %sum128 = add i128 %a, %b
  %sum8 = add i8 %c, %d
  %ext64 = zext i8 %sum8 to i64
  %ext128 = zext i64 %ext64 to i128
  %res = add i128 %sum128, %ext128
  ret i128 %res
}

define i64 @gep_load_select(ptr %base, i64 %idx, i64 %limit, i64 %fallback) nounwind {
entry:
  %cmp = icmp ult i64 %idx, %limit
  br i1 %cmp, label %in_bounds, label %out_of_bounds

in_bounds:
  %elt_ptr = getelementptr inbounds i64, ptr %base, i64 %idx
  %val = load i64, ptr %elt_ptr, align 8
  %gt = icmp ugt i64 %val, %fallback
  %sel = select i1 %gt, i64 %val, i64 %fallback
  br label %exit

out_of_bounds:
  br label %exit

exit:
  %ret = phi i64 [ %sel, %in_bounds ], [ %fallback, %out_of_bounds ]
  ret i64 %ret
}
