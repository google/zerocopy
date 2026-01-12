test_normalize! {
    DIR="D:\\repro"
    INPUT="tests\\ui\\nonzero_fail.rs"
"
error[E0080]: evaluation of constant value failed
 --> D:\\repro\\tests\\ui\\nonzero_fail.rs:7:10
  |
7 | #[derive(NonZeroRepr)]
  |          ^^^^^^^^^^^ the evaluated program panicked at 'expected non-zero discriminant expression', D:\\repro\\tests\\ui\\nonzero_fail.rs:7:10
" "
error[E0080]: evaluation of constant value failed
 --> tests/ui/nonzero_fail.rs:7:10
  |
7 | #[derive(NonZeroRepr)]
  |          ^^^^^^^^^^^ the evaluated program panicked at 'expected non-zero discriminant expression', $DIR/tests/ui/nonzero_fail.rs:7:10
"}
