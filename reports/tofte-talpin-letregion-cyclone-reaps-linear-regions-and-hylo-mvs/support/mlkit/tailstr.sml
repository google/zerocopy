(* P1c: tail loop threading a freshly allocated string accumulator of bounded length. *)
fun loop (0, s) = s
  | loop (n, s) = loop (n - 1, String.substring (s ^ Int.toString (n mod 10), 1, 8))
fun main n = loop (n, "abcdefgh")
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000000
val () = print (main n ^ "\n")
