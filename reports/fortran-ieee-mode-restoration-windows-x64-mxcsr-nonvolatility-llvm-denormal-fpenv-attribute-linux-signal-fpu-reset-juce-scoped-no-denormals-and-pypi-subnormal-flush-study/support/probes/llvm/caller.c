double callee_scale(double x);
double caller(double x) { return callee_scale(x) + 1.0; }
