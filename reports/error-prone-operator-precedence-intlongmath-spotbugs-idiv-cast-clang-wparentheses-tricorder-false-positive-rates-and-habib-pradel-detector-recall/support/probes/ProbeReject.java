// Cases that javac rejects at type-check time; all errors are expected.
// $ javac --release 17 -d /tmp/out ProbeReject.java
public class ProbeReject {
  static boolean c01_bitand_vs_eq(int a, int b, int c) { return a & b == c; }
  static boolean c12_chained_lt(int a, int b, int c) { return a < b < c; }
  static int c13_add_vs_ternary(int a, int b) { return a + (b > 0) ? 1 : 2; }
  static int c14_bitand_vs_ternary(int a, int b) { return a & (b > 0) ? 1 : 2; }
}
