#include <stdio.h>
#include <xmmintrin.h>
int main(void) { printf("MXCSR at main() = 0x%04x\n", _mm_getcsr()); return 0; }
