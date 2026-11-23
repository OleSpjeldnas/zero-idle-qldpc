#pragma once
#include <array>
#include <utility>
#include <vector>

namespace qldpc {
struct Code {
  int data_qubits;
  std::vector<std::vector<int>> hx, hz;
  std::vector<std::vector<std::pair<int, int>>> schedule;
};

// The Cayley table is row-major with identity at index zero. The six terms
// are ordered A then B. The twelve times are ordered A, B, B^T, A^T.
Code build_code(const std::vector<int> &cayley, int m, int a_weight,
                const std::array<int, 6> &terms,
                const std::array<int, 12> &times);
Code synthesize_cyclic(int n, int k, int distance);
} // namespace qldpc
