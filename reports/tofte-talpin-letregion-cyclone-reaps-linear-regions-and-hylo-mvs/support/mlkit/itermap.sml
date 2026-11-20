(* P2: iterate map over a list, threading the list through a tail call. *)
fun inc x = x + 1
fun iter (0, l) = l
  | iter (n, l) = iter (n - 1, List.map inc l)
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000
val l0 = List.tabulate (1000, fn i => i)
val r = iter (n, l0)
val () = print (Int.toString (List.foldl op+ 0 r) ^ "\n")
