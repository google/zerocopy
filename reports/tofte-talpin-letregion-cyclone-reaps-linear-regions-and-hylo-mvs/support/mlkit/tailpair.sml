(* P1b: tail loop threading a boxed pair (a Fibonacci-like state). *)
fun loop (0, p) = p
  | loop (n, (a, b)) = loop (n - 1, (b, (a + b) mod 1000000007))
fun main n = #1 (loop (n, (0, 1)))
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000000
val () = print (Int.toString (main n) ^ "\n")
