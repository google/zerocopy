test_normalize! {"
error: reached the recursion limit while instantiating `test::<Cons<Cons<Cons<Cons<Cons<...>>>>>>`
  --> src/main.rs:18:11
   |
18 |     _ => {test (n-1, i+1, Cons {head:2*i+1, tail:first}, Cons{head:i*i, tail:second})}
   |           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
note: `test` defined here
  --> src/main.rs:16:1
   |
16 | fn test<T:Dot> (n:isize, i:isize, first:T, second:T) ->isize {
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   = note: the full type name has been written to `/playground/target/debug/deps/playground-c53df771d95c66fb.c7a39e8d0dd9c781.long-type-16688711729771999621.txt`
           the full type name has been written to `/playground/target/debug/deps/playground-c53df771d95c66fb.c7a39e8d0dd9c781.long-type-16688711729771999621.txt`
" "
error: reached the recursion limit while instantiating `test::<Cons<Cons<Cons<Cons<Cons<...>>>>>>`
  --> src/main.rs:18:11
   |
18 |     _ => {test (n-1, i+1, Cons {head:2*i+1, tail:first}, Cons{head:i*i, tail:second})}
   |           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
note: `test` defined here
  --> src/main.rs:16:1
   |
16 | fn test<T:Dot> (n:isize, i:isize, first:T, second:T) ->isize {
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
"}
