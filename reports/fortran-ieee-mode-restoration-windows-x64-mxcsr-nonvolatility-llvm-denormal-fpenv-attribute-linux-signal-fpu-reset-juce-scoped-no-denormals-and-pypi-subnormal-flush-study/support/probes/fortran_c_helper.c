#include <fenv.h>
void c_set_downward(void) { fesetround(FE_DOWNWARD); }
int c_get_round(void) { return fegetround(); }
