#include "qldpc/code.hpp"
#include "qldpc/decoder.h"
#include <array>
#include <cstdio>
#include <cstdlib>
#include <new>
#include <vector>

static bool decoding = false;
static int allocations = 0;
void *operator new(std::size_t n) {
  allocations += decoding;
  if (void *p = std::malloc(n ? n : 1))
    return p;
  throw std::bad_alloc{};
}
void operator delete(void *p) noexcept { std::free(p); }
void operator delete(void *p, std::size_t) noexcept { std::free(p); }

int main() {
  auto code = qldpc::synthesize_cyclic(84, 8, 6);
  if (code.schedule.size() != 6 || code.hx.size() != 42)
    return 1;
  // A dense nonlocal syndrome exercises the native fallback at the word limit.
  constexpr int d = 2048, k = 64;
  std::vector<int> offsets{0}, indices;
  std::vector<float> costs;
  std::vector<uint64_t> masks;
  for (int i = 0; i < d; ++i) {
    for (int degree = 1; degree <= 3; ++degree) {
      for (int j = 0; j < degree; ++j)
        indices.push_back((i + 17 * j) % d);
      offsets.push_back(indices.size());
      costs.push_back(4.0f + degree);
      masks.push_back(1ULL << (i % 64));
    }
  }
  void *decoder =
      create_spacetime_decoder(d, costs.size(), k, offsets.data(),
                               indices.data(), costs.data(), masks.data());
  if (!decoder)
    return 2;
  std::array<uint8_t, d / 8> syn{};
  std::array<uint8_t, k> out{};
  int rc = 0;
  for (int stride : {1, 17, 33, 115}) {
    for (size_t i = 0; i < syn.size(); ++i)
      syn[i] = (i % stride == 0) ? uint8_t(i + 1) : 0;
    decoding = true;
    rc |= decode_spacetime_batch(decoder, syn.data(), 1, syn.size(), 8, .82f,
                                 .78f, out.data());
    decoding = false;
  }
  destroy_spacetime_decoder(decoder);
  std::printf("Native allocations during scalar decode: %d\n", allocations);
  return rc || allocations;
}
