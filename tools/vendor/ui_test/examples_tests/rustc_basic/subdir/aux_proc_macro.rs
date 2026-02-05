//@aux-build:../auxiliary/the_proc_macro.rs

use the_proc_macro::thing;

fn main() {
    thing!(cake);
    //~^ ERROR: cannot find value `cake` in this scope
}
