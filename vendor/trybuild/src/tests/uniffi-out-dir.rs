test_normalize! {
    DIR="/git/uniffi-rs/fixtures/uitests"
    WORKSPACE="/git/uniffi-rs"
    TARGET="/git/uniffi-rs/target"
"
error[E0277]: the trait bound `Arc<Counter>: FfiConverter` is not satisfied
   --> /git/uniffi-rs/target/debug/build/uniffi_uitests-1a51d46aecb559a7/out/counter.uniffi.rs:160:19
    |
160 |             match <std::sync::Arc<Counter> as uniffi::FfiConverter>::try_lift(ptr) {
    |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the trait `FfiConverter` is not implemented for `Arc<Counter>`
    |
    = help: the following implementations were found:
              <Arc<T> as FfiConverter>
    = note: required by `try_lift`
" "
error[E0277]: the trait bound `Arc<Counter>: FfiConverter` is not satisfied
 --> $OUT_DIR[uniffi_uitests]/counter.uniffi.rs
  |
  |             match <std::sync::Arc<Counter> as uniffi::FfiConverter>::try_lift(ptr) {
  |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the trait `FfiConverter` is not implemented for `Arc<Counter>`
  |
  = help: the following implementations were found:
            <Arc<T> as FfiConverter>
  = note: required by `try_lift`
"}
