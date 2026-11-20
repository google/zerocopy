(* P1: tail loop with a boxed real accumulator. n from command line. *)
fun loop (0, acc : real) = acc
  | loop (n, acc) = loop (n - 1, acc + 1.0)
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000000
val () = print (Real.toString (loop (n, 0.0)) ^ "\n")
