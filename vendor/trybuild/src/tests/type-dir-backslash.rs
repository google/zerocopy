test_normalize! {
    INPUT="tests/ui/compile-fail-3.rs"
"
error[E0277]: `*mut _` cannot be shared between threads safely
   --> /git/trybuild/test_suite/tests/ui/compile-fail-3.rs:7:5
    |
7   |     thread::spawn(|| {
    |     ^^^^^^^^^^^^^ `*mut _` cannot be shared between threads safely
    |
    = help: the trait `std::marker::Sync` is not implemented for `*mut _`
    = note: required because of the requirements on the impl of `std::marker::Send` for `&*mut _`
    = note: required because it appears within the type `[closure@/git/trybuild/test_suite/ui/compile-fail-3.rs:7:19: 9:6 x:&*mut _]`
" "
error[E0277]: `*mut _` cannot be shared between threads safely
 --> tests/ui/compile-fail-3.rs:7:5
  |
7 |     thread::spawn(|| {
  |     ^^^^^^^^^^^^^ `*mut _` cannot be shared between threads safely
  |
  = help: the trait `std::marker::Sync` is not implemented for `*mut _`
  = note: required because of the requirements on the impl of `std::marker::Send` for `&*mut _`
  = note: required because it appears within the type `[closure@$DIR/ui/compile-fail-3.rs:7:19: 9:6 x:&*mut _]`
"}
