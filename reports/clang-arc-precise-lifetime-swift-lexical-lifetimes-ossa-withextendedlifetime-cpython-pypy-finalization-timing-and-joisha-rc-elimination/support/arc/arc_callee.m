// arc_callee.m -- scenario D: an ARC-compiled callee whose parameter is the
// only remaining reference after an opaque call clears the global.
@class Obj;
extern Obj *g;
extern void release_global(void);   // non-ARC stub: g = NULL; objc_release(old)
extern void use(Obj *x);
extern void note(const char *msg);
void scenario_D_arc_callee(Obj *x) {
  release_global();
  use(x);              // parameter used after the other reference is dropped
  note("D: marker after use");
}
void scenario_D_driver(void) {
  scenario_D_arc_callee(g); // caller passes +0 (no retain for a plain argument)
}
