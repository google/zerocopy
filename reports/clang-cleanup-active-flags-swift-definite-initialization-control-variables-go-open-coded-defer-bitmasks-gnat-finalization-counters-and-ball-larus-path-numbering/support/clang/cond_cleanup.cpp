// Probe: conditional cleanups in a C++ compiler.
// Each function creates an object with a non-trivial (out-of-line) destructor
// on only some paths of one full-expression, so the compiler must decide at
// the end of the full-expression (and on the exceptional path) whether the
// destructor is owed.
struct S {
  int v;
  S(int);
  S(const S &);
  ~S();
};
int use(int);
bool pred(int);

// P1: temporary created in one arm of a conditional expression.
int t_cond(bool c, int x) { return use(c ? S(x).v : x); }

// P2: temporary created under a short-circuit operator.
int t_and(bool a, int x) { return (a && pred(S(x).v)) ? 1 : 0; }

// P3: two independent conditional temporaries in one full-expression.
int t_two(bool a, bool b, int x) {
  return use((a ? S(x).v : 0) + (b ? S(x + 1).v : 0));
}

// P4: lifetime-extended temporary chosen by a conditional.
int t_ext(bool c, int x) {
  const S &r = c ? S(x) : S(x + 1);
  return use(r.v);
}

// P4b: temporary bound to a reference member inside one arm only; its
// lifetime is extended to the enclosing scope, so the end-of-scope cleanup
// is owed only if that arm ran.
struct R {
  const S &s;
};
int t_ext2(bool c, int x, const S &g) {
  const R &r = c ? R{S(x)} : R{g};
  return use(r.s.v);
}

// P5: array initialised element by element; a later constructor may throw.
int t_arr(int x) {
  S a[4] = {S(x), S(x + 1), S(x + 2), S(x + 3)};
  return use(a[3].v);
}

// P6: new-expression whose constructor may throw (operator delete owed).
S *t_new(int x) { return new S(x); }

// B0: unconditional temporary (baseline, no flag expected).
int t_base(int x) { return use(S(x).v); }

// D1: hand-duplicated equivalent of t_cond (each arm owns its own cleanup).
int t_cond_dup(bool c, int x) {
  if (c) {
    S s(x);
    int r = use(s.v);
    return r;
  }
  return use(x);
}
