#pragma once
#include <cstdint>
namespace qldpc {
struct U128 {
  uint64_t lo = 0;
  uint64_t hi = 0;

  bool is_zero() const { return (lo | hi) == 0; }
  bool operator==(const U128 &o) const { return lo == o.lo && hi == o.hi; }
  bool operator!=(const U128 &o) const { return lo != o.lo || hi != o.hi; }
  bool operator<(const U128 &o) const {
    return (hi != o.hi) ? (hi < o.hi) : (lo < o.lo);
  }
  U128 operator^(const U128 &o) const { return {lo ^ o.lo, hi ^ o.hi}; }
  U128 &operator^=(const U128 &o) {
    lo ^= o.lo;
    hi ^= o.hi;
    return *this;
  }
  void set_bit(int b) {
    if (b < 64)
      lo |= (1ULL << b);
    else
      hi |= (1ULL << (b - 64));
  }
  int get_bit(int b) const {
    if (b < 64)
      return static_cast<int>((lo >> b) & 1ULL);
    return static_cast<int>((hi >> (b - 64)) & 1ULL);
  }
  int popcount() const {
    return __builtin_popcountll(lo) + __builtin_popcountll(hi);
  }
};

struct U256 {
  uint64_t w[4] = {0, 0, 0, 0};

  bool is_zero() const { return (w[0] | w[1] | w[2] | w[3]) == 0; }
  bool operator==(const U256 &o) const {
    return w[0] == o.w[0] && w[1] == o.w[1] && w[2] == o.w[2] && w[3] == o.w[3];
  }
  bool operator<(const U256 &o) const {
    for (int i = 3; i >= 0; --i) {
      if (w[i] != o.w[i])
        return w[i] < o.w[i];
    }
    return false;
  }
  U256 &operator^=(const U256 &o) {
    w[0] ^= o.w[0];
    w[1] ^= o.w[1];
    w[2] ^= o.w[2];
    w[3] ^= o.w[3];
    return *this;
  }
  void set_bit(int b) { w[b >> 6] |= (1ULL << (b & 63)); }
  int get_bit(int b) const {
    return static_cast<int>((w[b >> 6] >> (b & 63)) & 1ULL);
  }
};

static inline uint64_t splitmix64(uint64_t x) {
  x += 0x9e3779b97f4a7c15ULL;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}

} // namespace qldpc
