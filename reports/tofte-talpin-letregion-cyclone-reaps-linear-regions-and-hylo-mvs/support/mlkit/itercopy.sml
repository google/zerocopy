(* P3: same as P2 but the loop body copies the new list so the old one can die
   (the MLKit "copy idiom"). *)
fun inc x = x + 1
fun copy [] = []
  | copy (x :: xs) = x :: copy xs
fun iter (0, l) = l
  | iter (n, l) = iter (n - 1, copy (List.map inc l))
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000
val l0 = List.tabulate (1000, fn i => i)
val r = iter (n, l0)
val () = print (Int.toString (List.foldl op+ 0 r) ^ "\n")
