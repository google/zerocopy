# Silicon: A Viper Verifier Based on Symbolic Execution

<p align="center">
  <img width="512" height="144" alt="Silicon logo" src="docs/logo_name.png">
</p>

Silicon is a state-of-the-art, automated verifier based on symbolic execution,
and the default verifier of the
[Viper verification infrastructure](http://www.pm.inf.ethz.ch/research/viper.html).
Silicon's input language is the
[Viper intermediate verification language](http://pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=MuellerSchwerhoffSummers16.pdf):
a language in the spirit of Microsoft's Boogie, but with a higher level of
abstraction and a built-in notation of permissions, which makes Viper
well-suited for encoding and verifying properties of sequential and concurrent
programs with shared mutable state. Loads of details can (but don't need to) be
found in the
[PhD thesis of Malte Schwerhoff](http://pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=Schwerhoff16.pdf).

As an example, consider the following simple C++ program, which runs two threads
in parallel that increment a shared memory location and that uses a lock to
avoid race conditions:

```c++
#include <thread>
#include <mutex>
#include <assert.h>

struct Cell {
  int val;
};

void inc(Cell* c, std::mutex* guard) {
  guard->lock();
  
  int t = c->val;
  std::this_thread::sleep_for(std::chrono::seconds(1));
  c->val = t + 1;
  
  guard->unlock();
}

int main() {
  Cell* c = new Cell{0};
  std::mutex* guard = new std::mutex();
  
  std::thread t1 = std::thread(inc, c, guard);
  std::thread t2 = std::thread(inc, c, guard);

  t1.join();
  t2.join();
  
  guard->~mutex();
  assert(c->val == 2);

  return 0;
}
```

Such a program can be encoded in Viper, e.g. using an Owicki-Gries approach as
shown below, and Silicon can be used to automatically verify that the shared
memory location is indeed modified in an orderly manner.

```text
field val: Int
field t1: Int
field t2: Int

// Monitor/lock invariant associated with the shared cell
// Macro'ed for easy reuse
define guard_INV(c)
  acc(c.val) && acc(c.t1, 1/2) && acc(c.t2, 1/2) &&
  c.val == c.t1 + c.t2

// Precondition of inc
define inc_PRE(c, tid)
  (tid == 0 || tid == 1) &&
  (tid == 0 ? acc(c.t1, 1/2) : acc(c.t2, 1/2))
  
// Postcondition of inc
define inc_POST(c, tid, oldv)
  tid == 0 ? (acc(c.t1, 1/2) && c.t1 == oldv + 1)
            : (acc(c.t2, 1/2) && c.t2 == oldv + 1)

method inc(c: Ref, tid: Int)
  requires inc_PRE(c, tid)
  ensures  inc_POST(c, tid, tid == 0 ? old(c.t1) : old(c.t2))
{
  inhale guard_INV(c) // models guard.lock()
  
  c.val := c.val + 1
  
  if (tid == 0) { c.t1 := c.t1 + 1 }
  else { c.t2 := c.t2 + 1 }
  
  exhale guard_INV(c) // models guard.unlock()
}

method main() {
  var c: Ref
  c := new(val, t1, t2) // allocate real and ghost memory
  c.val := 0
  c.t1 := 0
  c.t2 := 0
  
  exhale guard_INV(c) // share the cell, i.e. create the guarding mutex
  
  label pre_fork
  exhale inc_PRE(c, 0) // fork thread 1
  exhale inc_PRE(c, 1) // fork thread 2
  
  inhale inc_POST(c, 0, old[pre_fork](c.t1)) // join thread 1
  inhale inc_POST(c, 1, old[pre_fork](c.t2)) // join thread 2
  
  inhale guard_INV(c) // unshare the cell, i.e. destroy the mutex
  
  assert c.val == 2;
}
```

# Getting Started

* Download the
  [Viper IDE](http://www.pm.inf.ethz.ch/research/viper/downloads.html)
  (based on Microsoft Visual Studio Code).

* Experiment with Viper using the
  [Viper online](http://viper.ethz.ch/examples/)
  web interface.

# Build Instructions

> See [the documentation wiki](https://github.com/viperproject/documentation/wiki) for instructions on how to try out or install the Viper tools.

* You need recent installations of
  1. the [sbt build tool](https://www.scala-sbt.org/)
  2. the [Z3 SMT solver](https://github.com/Z3Prover/z3/releases)
  3. (optional) the [cvc5 SMT solver](https://github.com/cvc5/cvc5/releases)
* Clone this repository *recursively* by running:  
`git clone --recursive https://github.com/viperproject/silicon`

And then, from the cloned directory, with the `Z3_EXE` environment variable set appropriately;  
* Compile and run with:  
  `sbt "run [options] <path to Viper file>"`  
  Or run all tests via `sbt test`
* Alternatively, for a faster startup without compilation each time, build a `.jar` file:  
  `sbt assembly`  
  And then run with:  
  `java -jar ./target/scala-*/silicon.jar [options] <path to Viper file>`

> We recommend IDEA IntelliJ for Scala development, but any IDE that supports sbt will do
