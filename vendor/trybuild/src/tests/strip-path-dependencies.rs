test_normalize! {"
error[E0277]: the trait bound `diesel::query_builder::SelectStatement<users::table, diesel::query_builder::select_clause::DefaultSelectClause, diesel::query_builder::distinct_clause::NoDistinctClause, diesel::query_builder::where_clause::WhereClause<diesel::expression::grouped::Grouped<diesel::expression::operators::Eq<posts::columns::id, diesel::expression::bound::Bound<diesel::sql_types::Integer, i32>>>>>: diesel::query_builder::IntoUpdateTarget` is not satisfied
  --> $DIR/update_requires_valid_where_clause.rs:21:12
   |
21 |     update(users::table.filter(posts::id.eq(1)));
   |            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the trait `diesel::query_builder::IntoUpdateTarget` is not implemented for `diesel::query_builder::SelectStatement<users::table, diesel::query_builder::select_clause::DefaultSelectClause, diesel::query_builder::distinct_clause::NoDistinctClause, diesel::query_builder::where_clause::WhereClause<diesel::expression::grouped::Grouped<diesel::expression::operators::Eq<posts::columns::id, diesel::expression::bound::Bound<diesel::sql_types::Integer, i32>>>>>`
   |
  ::: /home/user/documents/rust/diesel/diesel/src/query_builder/functions.rs:78:18
   |
78 | pub fn update<T: IntoUpdateTarget>(source: T) -> UpdateStatement<T::Table, T::WhereClause> {
   |                  ---------------- required by this bound in `diesel::update`
   |
   = help: the following implementations were found:
             <diesel::query_builder::SelectStatement<F, diesel::query_builder::select_clause::DefaultSelectClause, diesel::query_builder::distinct_clause::NoDistinctClause, W> as diesel::query_builder::IntoUpdateTarget>
" "
error[E0277]: the trait bound `diesel::query_builder::SelectStatement<users::table, diesel::query_builder::select_clause::DefaultSelectClause, diesel::query_builder::distinct_clause::NoDistinctClause, diesel::query_builder::where_clause::WhereClause<diesel::expression::grouped::Grouped<diesel::expression::operators::Eq<posts::columns::id, diesel::expression::bound::Bound<diesel::sql_types::Integer, i32>>>>>: diesel::query_builder::IntoUpdateTarget` is not satisfied
  --> $DIR/update_requires_valid_where_clause.rs:21:12
   |
21 |     update(users::table.filter(posts::id.eq(1)));
   |            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the trait `diesel::query_builder::IntoUpdateTarget` is not implemented for `diesel::query_builder::SelectStatement<users::table, diesel::query_builder::select_clause::DefaultSelectClause, diesel::query_builder::distinct_clause::NoDistinctClause, diesel::query_builder::where_clause::WhereClause<diesel::expression::grouped::Grouped<diesel::expression::operators::Eq<posts::columns::id, diesel::expression::bound::Bound<diesel::sql_types::Integer, i32>>>>>`
   |
  ::: $DIESEL/src/query_builder/functions.rs
   |
   | pub fn update<T: IntoUpdateTarget>(source: T) -> UpdateStatement<T::Table, T::WhereClause> {
   |                  ---------------- required by this bound in `diesel::update`
   |
   = help: the following implementations were found:
             <diesel::query_builder::SelectStatement<F, diesel::query_builder::select_clause::DefaultSelectClause, diesel::query_builder::distinct_clause::NoDistinctClause, W> as diesel::query_builder::IntoUpdateTarget>
"}
