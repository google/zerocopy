test_normalize! {"
error[E0277]: no implementation for `u8 >> &str`
 --> src/main.rs:2:20
  |
2 |     let _x = 42_u8 >> \"bar\";
  |                    ^^ no implementation for `u8 >> &str`
  |
  = help: the trait `Shr<&str>` is not implemented for `u8`
  = help: the following other types implement trait `Shr<Rhs>`:
            <&'a i128 as Shr<i128>>
            <&'a i128 as Shr<i16>>
            <&'a i128 as Shr<i32>>
            <&'a i128 as Shr<i64>>
            <&'a i128 as Shr<i8>>
            <&'a i128 as Shr<isize>>
            <&'a i128 as Shr<u128>>
            <&'a i128 as Shr<u16>>
          and 568 others
" "
error[E0277]: no implementation for `u8 >> &str`
 --> src/main.rs:2:20
  |
2 |     let _x = 42_u8 >> \"bar\";
  |                    ^^ no implementation for `u8 >> &str`
  |
  = help: the trait `Shr<&str>` is not implemented for `u8`
  = help: the following other types implement trait `Shr<Rhs>`:
            <&'a i128 as Shr<i128>>
            <&'a i128 as Shr<i16>>
            <&'a i128 as Shr<i32>>
            <&'a i128 as Shr<i64>>
            <&'a i128 as Shr<i8>>
            <&'a i128 as Shr<isize>>
            <&'a i128 as Shr<u128>>
            <&'a i128 as Shr<u16>>
          and $N others
"}
