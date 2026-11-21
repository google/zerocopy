// Precedence and arithmetic-kind probe for Java bytecode and source checkers.
// One case per method; the method name carries the case label.
// Cases that do not type-check in Java are listed in comments instead of code:
//   a & b == c  with int a,b,c  -> javac: bad operand types for binary operator '&'
//   a < b < c   with int a,b,c  -> javac: bad operand types for binary operator '<'
public class Probe {
  static int c02_shl_vs_add_const_left(int x, int y) { return x << 16 + y; }
  static int c03_shl_vs_add_const_right(int x, int y) { return x << y + 16; }
  static int c02b_shl_vs_add_const8(int x, int y) { return x << 8 + y; }
  static boolean c04_land_in_lor(boolean a, boolean b, boolean c) { return a && b || c; }
  static int c05_bitand_in_bitor(int a, int b, int c) { return a & b | c; }
  static int c06_bitxor_in_bitor(int a, int b, int c) { return a ^ b | c; }
  static int c08_bitand_vs_shl(int a, int b, int c) { return a & b << c; }
  static int c09_bitand_vs_add(int a, int b, int c) { return a & b + c; }
  static int c10_mul_vs_add_control(int a, int b, int c) { return a * b + c; }
  static int c11_rem_vs_shl(int a, int b) { return a % b << 2; }
  static boolean c01j_bitand_bool_vs_eq(boolean a, int b, int c) { return a & b == c; }
  static double c17_idiv_implicit_to_double(int i, int j) { double d = i / j; return d; }
  static double c18_idiv_cast_to_double(int i, int j) { return (double) (i / j); }
  static double c18b_idiv_const_folded() { return (double) (7 / 2); }
  static double c18c_ldiv_cast_to_double(long i, long j) { return (double) (i / j); }
  static double c18d_idiv_then_ceil(int i, int j) { return Math.ceil(i / j); }
  static long c19_imul_to_long(int i, int j) { long l = i * j; return l; }
  static long c19b_imul_param_const(int days) { return days * 24 * 3600 * 1000; }
  static long c20_imul_const_overflow() { long l = 24 * 60 * 60 * 1000 * 1000; return l; }
  static int c22_shr_vs_sub(int x, int y) { return x >> y - 1; }

  @Override
  public int hashCode() {
    return f << 16 + g;
  }

  int f;
  int g;

  static int c07_bitand_in_bitxor(int a, int b, int c) { return a & b ^ c; }
}
