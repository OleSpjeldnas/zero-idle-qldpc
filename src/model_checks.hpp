#pragma once
#include <cmath>
#include <cstdint>
#include <vector>

namespace qldpc {
inline bool valid_columns(int d, int m, int k, const int32_t *offsets,
                          const int32_t *indices, const float *llrs,
                          const uint64_t *masks) {
  if (d < 1 || d > 2048 || m < 0 || k < 0 || k > 64 || !offsets ||
      offsets[0] != 0)
    return false;
  if (m && (!llrs || !masks))
    return false;
  std::vector<int> seen(d, -1);
  for (int i = 0; i < m; ++i) {
    if (!std::isfinite(llrs[i]) || llrs[i] <= 0 ||
        offsets[i] > offsets[i + 1] || (k < 64 && (masks[i] >> k)))
      return false;
    for (int j = offsets[i]; j < offsets[i + 1]; ++j) {
      if (!indices || indices[j] < 0 || indices[j] >= d ||
          seen[indices[j]] == i)
        return false;
      seen[indices[j]] = i;
    }
  }
  return true;
}
} // namespace qldpc
