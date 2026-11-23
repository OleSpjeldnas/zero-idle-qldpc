#pragma once
#include <algorithm>
#include <cmath>
#include <cstdint>
#if defined(__aarch64__) && defined(__ARM_NEON)
#include <arm_neon.h>
#endif
namespace qldpc {
// Layered normalized min-sum. Each check visits each variable once. Cache
// the extrinsic value so the second sweep reads the contiguous message array.
inline void update_check(const int *columns, int count, bool syndrome,
                         float *post, float *message, float *extrinsic,
                         float scale, float damping) {
  float first = 35, second = 35;
  bool negative = syndrome;
  int i = 0;
#if defined(__aarch64__) && defined(__ARM_NEON)
  auto min1 = vdupq_n_f32(35), min2 = min1;
  uint32x4_t signs = vdupq_n_u32(0);
  for (; i + 4 <= count; i += 4) {
    float32x4_t values = {post[columns[i]], post[columns[i + 1]],
                          post[columns[i + 2]], post[columns[i + 3]]};
    auto v = vsubq_f32(values, vld1q_f32(message + i));
    vst1q_f32(extrinsic + i, v);
    signs = veorq_u32(signs, vcltq_f32(v, vdupq_n_f32(0)));
    auto mag = vabsq_f32(v);
    min2 = vminq_f32(min2, vmaxq_f32(min1, mag));
    min1 = vminq_f32(min1, mag);
  }
  negative ^= (vaddvq_u32(signs) & 1) != 0;
  float lanes[4];
  vst1q_f32(lanes, min1);
  second = vminvq_f32(min2);
  for (float lane : lanes) {
    second = std::min(second, std::max(first, lane));
    first = std::min(first, lane);
  }
#endif
  for (; i < count; ++i) {
    float v = post[columns[i]] - message[i];
    extrinsic[i] = v;
    negative ^= v < 0;
    float mag = std::fabs(v);
    second = std::min(second, std::max(first, mag));
    first = std::min(first, mag);
  }
  float signed_scale = negative ? -scale : scale;
  for (i = 0; i < count; ++i) {
    float v = extrinsic[i], old = message[i];
    float mag = std::fabs(v) == first ? second : first;
    float update =
        (1 - damping) * old + damping * signed_scale * (v < 0 ? -mag : mag);
    message[i] = update;
    post[columns[i]] += update - old;
  }
}
} // namespace qldpc
