(* P4b: FIFO loop rewritten so that pop's result is consumed without a local
   letregion wrapping the recursive call (uses a case on the queue directly). *)
fun run (0, f, b, s) = s
  | run (n, x :: f, b, s) = run (n - 1, f, n :: b, s + x)
  | run (n, [], b, s) = run (n, rev b, [], s)
fun main n = run (n, List.tabulate (1000, fn i => i), [], 0)
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000000
val () = print (Int.toString (main n) ^ "\n")
