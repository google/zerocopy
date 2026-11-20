(* P3b: copy idiom with the whole computation local to a function body
   (no top-level list binding). *)
fun inc x = x + 1
fun copy [] = []
  | copy (x :: xs) = x :: copy xs
fun iter (0, l) = l
  | iter (n, l) = iter (n - 1, copy (List.map inc l))
fun main n = List.foldl op+ 0 (iter (n, List.tabulate (1000, fn i => i)))
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000
val () = print (Int.toString (main n) ^ "\n")
