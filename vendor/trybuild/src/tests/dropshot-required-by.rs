test_normalize! {
    DIR="/git/dropshot/dropshot"
    WORKSPACE="/git/dropshot"
    INPUT="tests/fail/bad_endpoint4.rs"
"
error[E0277]: the trait bound `QueryParams: schemars::JsonSchema` is not satisfied
   --> /git/dropshot/dropshot/tests/fail/bad_endpoint4.rs:24:14
    |
24  |     _params: Query<QueryParams>,
    |              ^^^^^^^^^^^^^^^^^^ the trait `schemars::JsonSchema` is not implemented for `QueryParams`
    |
note: required by a bound in `dropshot::Query`
   --> /git/dropshot/dropshot/src/handler.rs:547:48
    |
547 | pub struct Query<QueryType: DeserializeOwned + JsonSchema + Send + Sync> {
    |                                                ^^^^^^^^^^ required by this bound in `dropshot::Query`
" "
error[E0277]: the trait bound `QueryParams: schemars::JsonSchema` is not satisfied
  --> tests/fail/bad_endpoint4.rs:24:14
   |
24 |     _params: Query<QueryParams>,
   |              ^^^^^^^^^^^^^^^^^^ the trait `schemars::JsonSchema` is not implemented for `QueryParams`
   |
note: required by a bound in `dropshot::Query`
  --> src/handler.rs
   |
   | pub struct Query<QueryType: DeserializeOwned + JsonSchema + Send + Sync> {
   |                                                ^^^^^^^^^^ required by this bound in `dropshot::Query`
"}
