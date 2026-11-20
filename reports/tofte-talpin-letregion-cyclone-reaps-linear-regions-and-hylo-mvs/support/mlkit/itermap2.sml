(* P2b: map iteration, local to a function body, no copy. *)
fun inc x = x + 1
fun iter (0, l) = l
  | iter (n, l) = iter (n - 1, List.map inc l)
fun main n = List.foldl op+ 0 (iter (n, List.tabulate (1000, fn i => i)))
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000
val () = print (Int.toString (main n) ^ "\n")
