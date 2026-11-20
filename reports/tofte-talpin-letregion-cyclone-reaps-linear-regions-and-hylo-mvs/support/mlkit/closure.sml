(* P5: escaping closures accumulated in a list; each closure captures a fresh
   boxed real. Only the last 10 closures are kept live by the program logic. *)
fun take10 (l, 0) = [] | take10 ([], _) = [] | take10 (x :: xs, k) = x :: take10 (xs, k - 1)
fun mk (r : real) = fn () => r + 1.0
fun run (0, fs) = fs
  | run (n, fs) = run (n - 1, take10 (mk (real n) :: fs, 10))
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000000
val fs = run (n, [])
val () = print (Real.toString (List.foldl (fn (f, a) => f () + a) 0.0 fs) ^ "\n")
