typedef unsigned long long U;
struct Pair { U a, b; };
struct Triple { U a, b, c; };
U abi_add(U a, U b) { return a + b; }
struct Pair abi_pair(struct Pair p) { return (struct Pair){ p.b, p.a }; }
struct Triple abi_triple(struct Triple p) { return (struct Triple){ p.c, p.b, p.a }; }
