typedef unsigned long long word;
extern word helper(word);
__declspec(noinline) word unwind_frame(word a) {
  volatile word scratch[4] = {a, a + 1, a + 2, a + 3};
  word result = helper(a);
  return result + scratch[0] + scratch[1] + scratch[2] + scratch[3];
}
