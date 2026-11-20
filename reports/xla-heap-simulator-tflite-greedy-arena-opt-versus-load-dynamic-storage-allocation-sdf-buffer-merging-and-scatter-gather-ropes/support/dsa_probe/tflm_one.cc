#include <cstdio>
#include <vector>
#include "tensorflow/lite/micro/memory_planner/greedy_memory_planner.h"
int main() {
  int sz[] = {6, 4, 3, 3}, st[] = {5, 1, 2, 3}, en[] = {5, 2, 4, 5};
  std::vector<unsigned char> scratch(4 * tflite::GreedyMemoryPlanner::per_buffer_size() + 64);
  tflite::GreedyMemoryPlanner p;
  p.Init(scratch.data(), scratch.size());
  for (int i = 0; i < 4; ++i) p.AddBuffer(sz[i], st[i], en[i]);
  std::printf("max=%zu\n", p.GetMaximumMemorySize());
  for (int i = 0; i < 4; ++i) { int o; p.GetOffsetForBuffer(i, &o); std::printf("buf%d size=%d [%d,%d] offset=%d\n", i, sz[i], st[i], en[i], o); }
  p.PrintMemoryPlan();
  return 0;
}
