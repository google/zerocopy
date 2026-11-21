// Out-of-line definitions for the conditional-cleanup probe, compiled in a
// separate translation unit (no LTO) so the optimizer cannot see through them.
struct S {
  int v;
  S(int);
  S(const S &);
  ~S();
};
volatile int sink;
S::S(int x) : v(x) { sink = x; }
S::S(const S &o) : v(o.v) { sink = o.v; }
S::~S() { sink = v; }
int use(int x) { sink = x; return x; }
bool pred(int x) { return (x & 1) != 0; }
