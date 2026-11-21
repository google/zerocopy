/* arc_stub_runtime.c -- logging stand-in for the Objective-C ARC runtime
 * entry points that clang emits for arc_probe.m. Toy runtime: objects are
 * never freed (so that "dead" objects can be inspected safely); deallocation
 * is modelled by setting a flag, printing "dealloc <name>", and zeroing
 * registered __weak slots. Compile as plain C (no ARC). */
#include <stdio.h>
#include <stdlib.h>

typedef struct Obj {
  long rc;
  int dead;
  const char *name;
  void **weak[8];
  int nweak;
} Obj;

void *g; /* strong global referenced by arc_probe.m */

static void dealloc_obj(Obj *o) {
  o->dead = 1;
  printf("    dealloc %s\n", o->name);
  for (int i = 0; i < o->nweak; i++)
    if (o->weak[i] && *o->weak[i] == o) *o->weak[i] = NULL;
  o->nweak = 0;
}

void *obj_new(const char *name) {
  Obj *o = calloc(1, sizeof *o);
  o->rc = 1;
  o->name = name;
  printf("    new %s rc=1\n", name);
  return o;
}

void *objc_retain(void *p) {
  if (p) { ((Obj *)p)->rc++; printf("    retain %s rc=%ld\n", ((Obj *)p)->name, ((Obj *)p)->rc); }
  return p;
}
void objc_release(void *p) {
  if (!p) return;
  Obj *o = p;
  o->rc--;
  printf("    release %s rc=%ld\n", o->name, o->rc);
  if (o->rc == 0) dealloc_obj(o);
}
void objc_storeStrong(void **loc, void *val) {
  void *old = *loc;
  objc_retain(val);
  *loc = val;
  objc_release(old);
}
void *objc_autorelease(void *p) { return p; } /* no pool: leak-free enough for the probe */
void *objc_retainAutorelease(void *p) { return objc_retain(p); }
void *objc_autoreleaseReturnValue(void *p) { return p; }
void *objc_retainAutoreleaseReturnValue(void *p) { return objc_retain(p); }
void *objc_retainAutoreleasedReturnValue(void *p) { return objc_retain(p); }
void *objc_unsafeClaimAutoreleasedReturnValue(void *p) { return p; }

static void reg_weak(void **slot, Obj *o) {
  if (o && !o->dead && o->nweak < 8) o->weak[o->nweak++] = slot;
}
void *objc_initWeak(void **slot, void *val) {
  Obj *o = val;
  if (o && o->dead) o = NULL;
  *slot = o;
  reg_weak(slot, o);
  return o;
}
void *objc_storeWeak(void **slot, void *val) { return objc_initWeak(slot, val); }
void *objc_loadWeakRetained(void **slot) {
  Obj *o = *slot;
  if (!o || o->dead) return NULL;
  return objc_retain(o);
}
void *objc_loadWeak(void **slot) { return *slot; }
void objc_destroyWeak(void **slot) { *slot = NULL; }
void objc_copyWeak(void **dst, void **src) { objc_initWeak(dst, *src); }
void objc_moveWeak(void **dst, void **src) { objc_initWeak(dst, *src); *src = NULL; }

void use(void *x) { printf("    use %s (dead=%d)\n", ((Obj *)x)->name, ((Obj *)x)->dead); }
void note(const char *msg) { printf("    -- %s\n", msg); }
void clear_global_and_check(void *x) {
  void *old = g;
  g = NULL;
  objc_release(old);
  printf("    callee: parameter object %s is %s\n", ((Obj *)x)->name,
         ((Obj *)x)->dead ? "DEALLOCATED (caller held no +1)" : "alive (caller held a +1)");
}

#ifndef ARC_STUB_NO_MAIN
void scenario_A_imprecise(void);
void scenario_A_precise(void);
void scenario_B_imprecise(void);
void scenario_B_precise(void);
void scenario_C_weak(void);

int main(void) {
  printf("scenario_A_imprecise\n"); scenario_A_imprecise();
  printf("scenario_A_precise\n");   scenario_A_precise();
  g = obj_new("B");
  printf("scenario_B_imprecise\n"); scenario_B_imprecise();
  g = obj_new("Bp");
  printf("scenario_B_precise\n");   scenario_B_precise();
  printf("scenario_C_weak\n");      scenario_C_weak();
  return 0;
}
#endif /* ARC_STUB_NO_MAIN */

/* Link-time stubs required by clang's gnustep-2.0 object-file format: a
 * module-load hook (no classes or selectors are defined, so nothing to
 * register) and an unwinding personality (never invoked: no exceptions). */
void __objc_load(void *init) { (void)init; }
int __gnustep_objc_personality_v0(void) { abort(); }
