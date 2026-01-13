test_normalize! {"
error[E0277]: the trait bound `QueryParams: serde::de::Deserialize<'de>` is not satisfied
   --> \\git\\trybuild\\test_suite\\tests\\ui\\error.rs:22:61
" "
error[E0277]: the trait bound `QueryParams: serde::de::Deserialize<'de>` is not satisfied
 --> tests/ui/error.rs:22:61
"}
