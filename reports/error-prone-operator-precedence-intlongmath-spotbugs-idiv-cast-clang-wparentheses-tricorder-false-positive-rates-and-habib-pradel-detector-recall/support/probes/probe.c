/* Precedence and arithmetic-kind probe for C compilers.
 * One case per function; the case label is in the function name so that
 * diagnostics can be matched to cases by line number.
 * Compile with: gcc -std=c17 -fsyntax-only [flags] probe.c
 */
int c01_bitand_vs_eq(int a, int b, int c) { return a & b == c; }
int c02_shl_vs_add_const_left(int x, int y) { return x << 16 + y; }
int c03_shl_vs_add_const_right(int x, int y) { return x << y + 16; }
int c04_land_in_lor(int a, int b, int c) { return a && b || c; }
int c05_bitand_in_bitor(int a, int b, int c) { return a & b | c; }
int c06_bitxor_in_bitor(int a, int b, int c) { return a ^ b | c; }
int c07_bitand_in_bitxor(int a, int b, int c) { return a & b ^ c; }
int c08_bitand_vs_shl(int a, int b, int c) { return a & b << c; }
int c09_bitand_vs_add(int a, int b, int c) { return a & b + c; }
int c10_mul_vs_add_control(int a, int b, int c) { return a * b + c; }
int c11_rem_vs_shl(int a, int b) { return a % b << 2; }
int c12_chained_lt(int a, int b, int c) { return a < b < c; }
int c13_add_vs_ternary(int a, int b) { return a + (b > 0) ? 1 : 2; }
int c14_bitand_vs_ternary(int a, int b) { return a & (b > 0) ? 1 : 2; }
int c15_lnot_vs_eq(int a, int b) { return !a == b; }
int c16_assign_in_cond(int a, int b) { if (a = b) return 1; return 0; }
double c17_idiv_implicit_to_double(int i, int j) { double d = i / j; return d; }
double c18_idiv_cast_to_double(int i, int j) { return (double)(i / j); }
long long c19_imul_to_long(int i, int j) { long long l = i * j; return l; }
long long c20_imul_const_overflow(void) { long long l = 24 * 60 * 60 * 1000 * 1000; return l; }
int c21_bitor_vs_ne(int a, int b, int c) { return a | b != c; }
int c22_shr_vs_sub(int x, int y) { return x >> y - 1; }
int c02b_shl_vs_add_const8(int x, int y) { return x << 8 + y; }
double c18b_idiv_const_cast_to_double(void) { return (double)(7 / 2); }
