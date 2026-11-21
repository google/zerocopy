#include <stdio.h>
extern void *g; void *obj_new(const char *); void objc_release(void *);
void release_global(void) { void *o = g; g = NULL; objc_release(o); }
void scenario_D_driver(void);
int main(void) { g = obj_new("D"); printf("scenario_D\n"); scenario_D_driver(); return 0; }
