(* P4: a FIFO whose elements die asynchronously: push k, pop k, repeated.
   Live size is bounded by w; total allocated grows with n. *)
type q = int list * int list
fun push (x, (f, b) : q) : q = (f, x :: b)
fun pop ((x :: f, b) : q) = (x, (f, b))
  | pop ([], []) = raise Empty
  | pop ([], b) = pop (rev b, [])
fun run (0, q, s) = s
  | run (n, q, s) =
      let val q1 = push (n, q)
          val (x, q2) = pop q1
      in run (n - 1, q2, s + x) end
val n = case CommandLine.arguments () of [s] => valOf (Int.fromString s) | _ => 1000000
fun fill (0, q) = q | fill (k, q) = fill (k - 1, push (k, q))
val () = print (Int.toString (run (n, fill (100, ([], [])), 0)) ^ "\n")
