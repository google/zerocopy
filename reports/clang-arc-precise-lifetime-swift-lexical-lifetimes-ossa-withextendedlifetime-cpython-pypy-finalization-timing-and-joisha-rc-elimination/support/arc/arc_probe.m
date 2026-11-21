// arc_probe.m -- release-timing probe for clang's Objective-C ARC.
// Compiled with ARC; linked against arc_stub_runtime.c, a tiny logging
// stand-in for the Objective-C runtime's reference-counting entry points
// (it is NOT Apple's or GNUstep's runtime; only objc_retain/objc_release/
// weak entry points are provided). No message sends are used, so no class
// registration is needed: objects are opaque `Obj *` pointers, which ARC
// treats as retainable object pointers.
@class Obj;

// +1 result (ns_returns_retained): no retain is emitted by the caller.
extern Obj *obj_new(const char *name) __attribute__((ns_returns_retained));
// Opaque functions defined in the non-ARC stub translation unit.
extern void use(Obj *x);           // reads the object (prints "use")
extern void note(const char *msg);  // prints a marker line
extern void clear_global_and_check(Obj *x); // releases g, then reports x's state
extern Obj *g;                      // strong global, managed by the stub TU

// A: x holds the only reference (+1 from obj_new); last use, then a marker.
void scenario_A_imprecise(void) {
  Obj *x = obj_new("A");
  use(x);
  note("A: marker after last use");
}

void scenario_A_precise(void) {
  __attribute__((objc_precise_lifetime)) Obj *x = obj_new("Ap");
  use(x);
  note("Ap: marker after last use");
}

// B: the spec's own motivating shape: copy a value out of a strong location
// (retain), then make an opaque call that releases that location.
void scenario_B_imprecise(void) {
  Obj *x = g;                  // objc_retain at -O0
  clear_global_and_check(x);   // callee releases g, then inspects x
  note("B: marker after call");
}

void scenario_B_precise(void) {
  __attribute__((objc_precise_lifetime)) Obj *x = g;
  clear_global_and_check(x);
  note("Bp: marker after call");
}

// C: weak reference observes whether the strong local has been released.
void scenario_C_weak(void) {
  Obj *x = obj_new("C");
  __weak Obj *w = x;
  use(x);
  note("C: before weak load");
  Obj *y = w;
  note(y ? "C: weak load -> object (still alive)" : "C: weak load -> nil (already released)");
}
