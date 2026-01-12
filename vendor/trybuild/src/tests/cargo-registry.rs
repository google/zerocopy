test_normalize! {"
error[E0277]: the trait bound `Thread: serde::de::Deserialize<'_>` is not satisfied
    --> src/main.rs:2:36
     |
2    |     let _ = serde_json::from_str::<std::thread::Thread>(\"???\");
     |                                    ^^^^^^^^^^^^^^^^^^^ the trait `serde::de::Deserialize<'_>` is not implemented for `Thread`
     |
    ::: /home/ferris/.cargo/registry/src/github.com-1ecc6299db9ec823/serde_json-1.0.64/src/de.rs:2584:8
     |
2584 |     T: de::Deserialize<'a>,
     |        ------------------- required by this bound in `serde_json::from_str`

For more information about this error, try `rustc --explain E0277`.
error: could not compile `testing` due to previous error
" "
error[E0277]: the trait bound `Thread: serde::de::Deserialize<'_>` is not satisfied
 --> src/main.rs:2:36
  |
2 |     let _ = serde_json::from_str::<std::thread::Thread>(\"???\");
  |                                    ^^^^^^^^^^^^^^^^^^^ the trait `serde::de::Deserialize<'_>` is not implemented for `Thread`
  |
 ::: $CARGO/serde_json-1.0.64/src/de.rs
  |
  |     T: de::Deserialize<'a>,
  |        ------------------- required by this bound in `serde_json::from_str`
"}
