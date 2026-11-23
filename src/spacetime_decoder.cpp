#include "bits.hpp"
#include "min_sum.hpp"
#include "model_checks.hpp"
#include "qldpc/decoder.h"
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <map>
#include <numeric>
#include <set>
#include <tuple>
#include <unordered_map>
#include <vector>

namespace {
using namespace qldpc;
struct HashEntry1 {
  uint64_t key_hash = 0;
  int mech_id = -1;
};

struct FastSpaceTimeDecoder {
  int num_det = 0;
  int num_mech = 0;
  int num_obs = 0;
  int syn_words = 0;
  float min_pos_llr = 10.0f;
  double pair_floor, triple_floor, four_floor;
  std::vector<uint64_t> col_hash;
  std::vector<uint64_t> detector_hash, cooccurrence;
  int max_col_weight = 0;
  std::vector<int> next_equal;

  std::vector<float> llr;
  std::vector<float> llr_pos;
  std::vector<float> llr_bp;
  std::vector<uint64_t> obs_mask;
  std::vector<uint64_t> col_bits;

  std::vector<int> col_ptr, col_det;
  std::vector<int> det_ptr;
  std::vector<int> det_mech;

  uint64_t ht_mask = 0;
  std::vector<HashEntry1> ht1;

  struct LocalColumn {
    int id;
    float score;
  };
  struct LocalWork {
    std::vector<uint16_t> hits;
    std::vector<int> touched;
    std::vector<LocalColumn> columns;
  };
  struct Workspace {
    LocalWork quick;
    std::vector<float> post, messages, scores, extrinsic;
    std::vector<uint8_t> syndrome;
    std::vector<int> hard, order, hits, local, ptr, edges, cursor, nonpiv,
        direct, other, active;
    std::vector<char> fringe;
    std::vector<double> slack;
    std::vector<uint64_t> basis, combinations, delta;
    void prepare(int d, int m, int e, int w) {
      quick.hits.resize(m);
      quick.touched.reserve(m);
      quick.columns.reserve(m);
      post.resize(m);
      messages.reserve(e);
      extrinsic.resize(e);
      scores.resize(m);
      syndrome.resize(d);
      hard.reserve(m);
      order.resize(m);
      hits.resize(m);
      local.reserve(m);
      ptr.resize(d + 1);
      edges.reserve(e);
      cursor.resize(d + 1);
      fringe.resize(d);
      slack.resize(m);
      basis.resize(d * w);
      combinations.resize(d * w);
      delta.reserve(84 * w);
      for (auto *list : {&nonpiv, &direct, &other, &active})
        list->reserve(84);
    }
  } work;
  bool quick_osd(const uint64_t *target, int weight, LocalWork &scratch,
                 double &best_cost, uint64_t &best_obs) const {
    if (weight < 1)
      return false;
    auto &hits = scratch.hits;
    hits.assign(num_mech, 0);
    auto &touched = scratch.touched;
    touched.clear();
    int fired[2048], nf = 0;
    for (int w = 0; w < syn_words; ++w) {
      for (uint64_t bits = target[w]; bits; bits &= bits - 1) {
        int d = 64 * w + __builtin_ctzll(bits);
        fired[nf++] = d;
        for (int j = det_ptr[d]; j < det_ptr[d + 1]; ++j) {
          int m = det_mech[j];
          if (!hits[m])
            touched.push_back(m);
          ++hits[m];
        }
      }
    }
    auto &cols = scratch.columns;
    cols.clear();
    for (int m : touched) {
      int inside = hits[m], outside = col_ptr[m + 1] - col_ptr[m] - inside;
      if (outside > 2 || (inside == 1 && outside > 1))
        continue;
      float score = llr_pos[m] / inside + 1.4f * outside;
      cols.push_back({m, score});
    }
    if (cols.empty())
      return false;
    int limit = std::min<int>(cols.size(), std::min(360, 48 + 8 * weight));
    auto less = [](const LocalColumn &a, const LocalColumn &b) {
      return a.score != b.score ? a.score < b.score : a.id < b.id;
    };
    if (limit < int(cols.size()))
      std::nth_element(cols.begin(), cols.begin() + limit, cols.end(), less);
    std::sort(cols.begin(), cols.begin() + limit, less);
    // A full syndrome column, and its exact representation in original pivots.
    uint64_t rows[128][32];
    U128 combos[128];
    float cost[128];
    uint64_t obs[128];
    int slot[2048];
    std::fill(slot, slot + num_det, -1);
    struct Move {
      U128 change;
      int id;
    };
    Move moves[112];
    int nm = 0, rank = 0;
    auto reduce = [&](uint64_t *bits, U128 &combination) {
      for (int w = 0; w < syn_words; ++w)
        while (bits[w]) {
          int d = 64 * w + __builtin_ctzll(bits[w]), i = slot[d];
          if (i < 0)
            return d;
          for (int j = w; j < syn_words; ++j)
            bits[j] ^= rows[i][j];
          combination ^= combos[i];
        }
      return -1;
    };
    for (int j = 0; j < limit; ++j) {
      int id = cols[j].id;
      uint64_t bits[32];
      U128 comb;
      std::memcpy(bits, &col_bits[size_t(id) * syn_words], syn_words * 8);
      int pivot = reduce(bits, comb);
      if (pivot < 0) {
        if (nm < 112)
          moves[nm++] = {comb, id};
        continue;
      }
      if (rank == 128)
        continue;
      slot[pivot] = rank;
      std::memcpy(rows[rank], bits, syn_words * 8);
      comb.set_bit(rank);
      combos[rank] = comb;
      cost[rank] = llr_pos[id];
      obs[rank++] = obs_mask[id];
    }
    uint64_t bits[32];
    U128 solution;
    std::memcpy(bits, target, syn_words * 8);
    if (reduce(bits, solution) >= 0)
      return false;
    auto weight_cost = [&](U128 x) {
      double c = 0;
      for (auto w = x.lo; w; w &= w - 1)
        c += cost[__builtin_ctzll(w)];
      for (auto w = x.hi; w; w &= w - 1)
        c += cost[64 + __builtin_ctzll(w)];
      return c;
    };
    auto evaluate = [&](U128 x, double offset, uint64_t mask) {
      double c = offset + weight_cost(x);
      if (c >= best_cost)
        return;
      for (auto w = x.lo; w; w &= w - 1)
        mask ^= obs[__builtin_ctzll(w)];
      for (auto w = x.hi; w; w &= w - 1)
        mask ^= obs[64 + __builtin_ctzll(w)];
      best_cost = c;
      best_obs = mask;
    };
    evaluate(solution, 0, 0);
    // A second independent improvement can be made on top of the best first
    // move.
    int best_first = -1;
    double first_cost = weight_cost(solution);
    for (int i = 0; i < nm; ++i) {
      auto move = moves[i];
      auto x = solution ^ move.change;
      double c = weight_cost(x) + llr_pos[move.id];
      if (c < first_cost) {
        best_first = i;
        first_cost = c;
      }
      if (c <= best_cost)
        evaluate(x, llr_pos[move.id], obs_mask[move.id]);
    }
    for (int i = 0; i < std::min(nm, 18); ++i) {
      auto u = moves[i];
      for (int j = i + 1; j < std::min(nm, 18); ++j) {
        auto v = moves[j];
        evaluate(solution ^ u.change ^ v.change,
                 double(llr_pos[u.id]) + llr_pos[v.id],
                 obs_mask[u.id] ^ obs_mask[v.id]);
      }
    }
    if (best_first >= 0) {
      auto u = moves[best_first];
      for (int j = 0; j < nm; ++j)
        if (j != best_first) {
          auto v = moves[j];
          evaluate(solution ^ u.change ^ v.change,
                   double(llr_pos[u.id]) + llr_pos[v.id],
                   obs_mask[u.id] ^ obs_mask[v.id]);
        }
    }
    // Fractional detector prices. Each incident column pays no more than its
    // cost over its fired checks. The additive acceptance margin is heuristic.
    double dual = 0;
    for (int i = 0; i < nf; ++i) {
      int d = fired[i];
      float price = 1e30f;
      for (int j = det_ptr[d]; j < det_ptr[d + 1]; ++j) {
        int m = det_mech[j];
        price = std::min(price, llr_pos[m] / hits[m]);
      }
      dual += price;
    }
    return best_cost <= dual + 3.25 * min_pos_llr;
  }

  // A single column cannot cover two chosen checks. Four such fired checks
  // rule out every triple irrespective of the mechanism costs.
  bool exceeds_count(const uint64_t *target, int limit) const {
    uint64_t remaining[32];
    std::copy_n(target, syn_words, remaining);
    int count = 0;
    for (int w = 0; w < syn_words; ++w)
      while (remaining[w]) {
        if (++count > limit)
          return true;
        int d = 64 * w + __builtin_ctzll(remaining[w]);
        const auto *covered = cooccurrence.data() + size_t(d) * syn_words;
        for (int j = w; j < syn_words; ++j)
          remaining[j] &= ~covered[j];
      }
    return false;
  }

  bool low_weight(const uint64_t *syn_words, int syn_weight,
                  double &best_fast_cost, uint64_t &best_fast_obs) const {
    const int W = this->syn_words, M = num_mech;
    // 1. Strict cost-floor 1-Mechanism Fast Path
    uint64_t target_hash = hash_words(syn_words);
    int m_single = lookup_hashed(syn_words, target_hash);
    best_fast_cost = (m_single >= 0) ? llr_pos[m_single] : HUGE_VAL;
    best_fast_obs = (m_single >= 0) ? obs_mask[m_single] : 0ULL;
    bool ambiguous = false;
    for (int m = m_single; m >= 0; m = next_equal[m]) {
      ambiguous |= best_fast_obs != obs_mask[m];
      best_fast_obs = std::min(best_fast_obs, obs_mask[m]);
    }
    if (m_single >= 0 && !ambiguous && best_fast_cost < pair_floor) {
      return true;
    }

    if (exceeds_count(syn_words, 3))
      return false;

    // 2. Strict cost-floor 2-Mechanism Meet-in-the-Middle Fast Path
    int first_d = -1;
    for (int w = 0; w < W; ++w) {
      if (syn_words[w]) {
        first_d = (w << 6) + __builtin_ctzll(syn_words[w]);
        break;
      }
    }

    if (first_d >= 0 && syn_weight <= 2 * max_col_weight) {
      int p0 = det_ptr[first_d], p1 = det_ptr[first_d + 1];
      uint64_t rem_w[32];
      for (int p = p0; p < p1; ++p) {
        int m1 = det_mech[p];
        float c1 = llr_pos[m1];
        if (c1 >= best_fast_cost)
          continue;
        const uint64_t *cb1 = &col_bits[static_cast<size_t>(m1) * W];
        for (int w = 0; w < W; ++w)
          rem_w[w] = syn_words[w] ^ cb1[w];
        int m2 = lookup_hashed(rem_w, target_hash ^ col_hash[m1]);
        for (; m2 >= 0; m2 = next_equal[m2]) {
          double cost = double(c1) + llr_pos[m2];
          uint64_t mask = obs_mask[m1] ^ obs_mask[m2];
          if (cost < best_fast_cost) {
            best_fast_cost = cost;
            best_fast_obs = mask;
            ambiguous = false;
          } else if (cost == best_fast_cost && mask != best_fast_obs) {
            ambiguous = true;
            best_fast_obs = std::min(best_fast_obs, mask);
          }
        }
      }
      if (!ambiguous && best_fast_cost < triple_floor) {
        return true;
      }
    }

    // Each compatible triple covers an odd detector with at least one member.
    // After that choice, a second odd detector anchors the residual pair.
    // Equality of packed columns confirms every hash hit.
    if (syn_weight <= 3 * max_col_weight) {
      auto rarest = [&](const uint64_t *bits) {
        int chosen = -1, degree = M + 1;
        for (int w = 0; w < W; ++w) {
          uint64_t word = bits[w];
          while (word) {
            int d = 64 * w + __builtin_ctzll(word);
            int size = det_ptr[d + 1] - det_ptr[d];
            if (size < degree) {
              chosen = d;
              degree = size;
            }
            word &= word - 1;
          }
        }
        return chosen;
      };
      int anchor = rarest(syn_words);
      for (int i = det_ptr[anchor]; i < det_ptr[anchor + 1]; ++i) {
        int a = det_mech[i];
        double ca = llr_pos[a];
        if (ca + pair_floor > best_fast_cost)
          continue;
        const auto *acol = &col_bits[size_t(a) * W];
        uint64_t residual[32];
        int weight = 0;
        for (int w = 0; w < W; ++w) {
          residual[w] = syn_words[w] ^ acol[w];
          weight += __builtin_popcountll(residual[w]);
        }
        if (!weight || weight > 2 * max_col_weight ||
            exceeds_count(residual, 2))
          continue;
        int pivot = rarest(residual);
        uint64_t residual_hash = target_hash ^ col_hash[a];
        for (int j = det_ptr[pivot]; j < det_ptr[pivot + 1]; ++j) {
          int b = det_mech[j];
          double cab = ca + llr_pos[b];
          if (b == a || cab + min_pos_llr > best_fast_cost)
            continue;
          uint64_t h = residual_hash ^ col_hash[b];
          auto bucket = h & ht_mask;
          while (ht1[bucket].mech_id >= 0 && ht1[bucket].key_hash != h)
            bucket = (bucket + 1) & ht_mask;
          if (ht1[bucket].mech_id < 0)
            continue;
          const auto *bcol = &col_bits[size_t(b) * W];
          uint64_t complement[32];
          for (int w = 0; w < W; ++w)
            complement[w] = residual[w] ^ bcol[w];
          for (int c = lookup_hashed(complement, h); c >= 0;
               c = next_equal[c]) {
            if (c == a || c == b)
              continue;
            double cost = cab + llr_pos[c];
            uint64_t obs = obs_mask[a] ^ obs_mask[b] ^ obs_mask[c];
            if (cost < best_fast_cost) {
              best_fast_cost = cost;
              best_fast_obs = obs;
              ambiguous = false;
            } else if (cost == best_fast_cost && obs != best_fast_obs) {
              best_fast_obs = std::min(best_fast_obs, obs);
              ambiguous = true;
            }
          }
        }
      }
      if (!ambiguous && best_fast_cost < four_floor && best_fast_cost < 1e29) {
        return true;
      }
    }

    return false;
  }
  // Row q lists which columns at check d also touch q. A cache-linear
  // accumulation gives all overlap counts for an entire beam expansion.
  std::vector<int> overlap_offsets;
  std::vector<unsigned char> overlap_rows;
  void prepare_overlap() {
    if (num_det > 512 || max_col_weight > 255)
      return;
    size_t bytes = 0;
    for (int d = 0; d < num_det; d++) {
      int count = det_ptr[d + 1] - det_ptr[d];
      if (count > 512)
        return;
      for (int w = 0; w < syn_words; w++)
        bytes += size_t(count) *
                 __builtin_popcountll(cooccurrence[size_t(d) * syn_words + w]);
    }
    if (bytes > 16 * 1024 * 1024)
      return;
    overlap_offsets.assign(size_t(num_det) * num_det, -1);
    overlap_rows.reserve(bytes);
    for (int d = 0; d < num_det; d++) {
      auto *offsets = overlap_offsets.data() + size_t(d) * num_det;
      int first = det_ptr[d], count = det_ptr[d + 1] - first;
      for (int e = 0; e < count; e++) {
        int m = det_mech[first + e];
        for (int j = col_ptr[m]; j < col_ptr[m + 1]; j++) {
          int q = col_det[j];
          if (offsets[q] < 0) {
            offsets[q] = overlap_rows.size();
            overlap_rows.resize(overlap_rows.size() + count);
          }
          overlap_rows[offsets[q] + e] = 1;
        }
      }
    }
  }
  // A bounded beam on residual detector sets. Expansion at one fired check
  // keeps the frontier small. Only exact zero residuals provide predictions.
  template <size_t Capacity>
  bool repair_beam(const uint64_t *target, int weight, double &best,
                   uint64_t &logical) const {
    constexpr int width = 5;
    struct Node {
      std::array<uint64_t, Capacity> bits{};
      uint64_t mask = 0, hash = 0;
      float cost = 0, estimate = 0;
      int weight = 0, last = -1;
    };
    Node current[width]{}, next[width]{};
    std::copy_n(target, syn_words, current[0].bits.begin());
    current[0].weight = weight;
    current[0].hash = hash_words(target);
    int size = 1;
    for (int step = 0; step < std::min(48, weight + 4); ++step) {
      int used = 0;
      for (int i = 0; i < size; ++i) {
        const auto &node = current[i];
        int anchor = -1, degree = num_mech + 1;
        for (int w = 0; w < syn_words; ++w)
          for (auto v = node.bits[w]; v; v &= v - 1) {
            int d = w * 64 + __builtin_ctzll(v);
            if (det_ptr[d + 1] - det_ptr[d] < degree) {
              degree = det_ptr[d + 1] - det_ptr[d];
              anchor = d;
            }
          }
        if (anchor < 0)
          continue;
        unsigned char overlaps[512] = {};
        if (!overlap_offsets.empty()) {
          const auto *offsets =
              overlap_offsets.data() + size_t(anchor) * num_det;
          int count = det_ptr[anchor + 1] - det_ptr[anchor];
          for (int w = 0; w < syn_words; w++) {
            for (uint64_t v = node.bits[w] &
                              cooccurrence[size_t(anchor) * syn_words + w];
                 v; v &= v - 1) {
              int row = offsets[64 * w + __builtin_ctzll(v)];
              if (row < 0)
                continue;
              const auto *hits = overlap_rows.data() + row;
              for (int j = 0; j < count; j++)
                overlaps[j] += hits[j];
            }
          }
        }
        for (int e = det_ptr[anchor]; e < det_ptr[anchor + 1]; ++e) {
          int id = det_mech[e];
          float cost = node.cost + llr_pos[id];
          if (cost >= best || id == node.last)
            continue;
          int wt = node.weight;
          if (!overlap_offsets.empty())
            wt += col_ptr[id + 1] - col_ptr[id] -
                  2 * overlaps[e - det_ptr[anchor]];
          else
            for (int j = col_ptr[id]; j < col_ptr[id + 1]; ++j) {
              int d = col_det[j];
              wt += ((node.bits[d / 64] >> (d % 64)) & 1) ? -1 : 1;
            }
          if (wt > node.weight + 1)
            continue;
          uint64_t mask = node.mask ^ obs_mask[id];
          if (!wt) {
            best = cost;
            logical = mask;
            continue;
          }
          float estimate = cost + wt * min_pos_llr * .9f;
          if (used == width && estimate >= next[used - 1].estimate)
            continue;
          uint64_t hash = node.hash ^ col_hash[id];
          Node proposal;
          for (int w = 0; w < syn_words; ++w)
            proposal.bits[w] =
                node.bits[w] ^ col_bits[size_t(id) * syn_words + w];
          proposal.mask = mask;
          proposal.cost = cost;
          proposal.estimate = estimate;
          proposal.hash = hash;
          proposal.weight = wt;
          proposal.last = id;
          int j = 0;
          for (; j < used; ++j)
            if (next[j].hash == hash && next[j].bits == proposal.bits)
              break;
          if (j < used && next[j].cost <= cost)
            continue;
          if (j == used) {
            j = std::min(used, width - 1);
            used = std::min(used + 1, width);
          }
          while (j > 0 && next[j - 1].estimate > estimate) {
            next[j] = next[j - 1];
            --j;
          }
          next[j] = proposal;
        }
      }
      if (std::isfinite(best))
        return true;
      if (!used)
        break;
      std::copy_n(next, used, current);
      size = used;
    }
    return false;
  }
  bool repair(const uint64_t *target, int weight, double &best,
              uint64_t &logical) const {
    if (syn_words <= 8)
      return repair_beam<8>(target, weight, best, logical);
    return repair_beam<32>(target, weight, best, logical);
  }
  // Extract fully contained columns, then repair overlapping fault clusters
  // on the residual. Every returned incumbent reproduces the input syndrome.
  bool peel(const uint64_t *target, int weight, double &best, uint64_t &mask) {
    uint64_t residual[32];
    std::copy_n(target, syn_words, residual);
    auto &hits = work.hits;
    std::fill(hits.begin(), hits.end(), 0);
    auto &pool = work.local;
    pool.clear();
    for (int w = 0; w < syn_words; ++w)
      for (auto v = target[w]; v; v &= v - 1) {
        int d = w * 64 + __builtin_ctzll(v);
        for (int j = det_ptr[d]; j < det_ptr[d + 1]; ++j) {
          int id = det_mech[j];
          if (++hits[id] == col_ptr[id + 1] - col_ptr[id])
            pool.push_back(id);
        }
      }
    std::sort(pool.begin(), pool.end(), [&](int a, int b) {
      float wa = llr_pos[a] * hits[b], wb = llr_pos[b] * hits[a];
      return wa != wb ? wa < wb : a < b;
    });
    double spent = 0;
    uint64_t logical = 0;
    int remaining = weight;
    for (int id : pool) {
      if (remaining <= 3)
        break;
      bool inside = true;
      for (int j = col_ptr[id]; j < col_ptr[id + 1]; ++j) {
        int d = col_det[j];
        if (!(residual[d / 64] & (1ULL << (d % 64)))) {
          inside = false;
          break;
        }
      }
      if (!inside)
        continue;
      for (int j = col_ptr[id]; j < col_ptr[id + 1]; ++j) {
        int d = col_det[j];
        residual[d / 64] ^= 1ULL << (d % 64);
      }
      remaining -= hits[id];
      spent += llr_pos[id];
      logical ^= obs_mask[id];
    }
    if (remaining == weight || spent >= best)
      return false;
    double rest = HUGE_VAL;
    uint64_t obs = 0;
    if (remaining == 0)
      rest = 0;
    else {
      if (!low_weight(residual, remaining, rest, obs) &&
          !quick_osd(residual, remaining, work.quick, rest, obs) &&
          !repair(residual, remaining, rest, obs))
        return false;
    }
    if (spent + rest < best) {
      best = spent + rest;
      mask = logical ^ obs;
    }
    // Tighten a feasible dual price vector before accepting the heuristic.
    auto &slack = work.slack;
    std::copy(llr_pos.begin(), llr_pos.end(), slack.begin());
    double dual = 0;
    for (int w = 0; w < syn_words; ++w)
      for (auto v = target[w]; v; v &= v - 1) {
        int d = 64 * w + __builtin_ctzll(v);
        double price = HUGE_VAL;
        for (int j = det_ptr[d]; j < det_ptr[d + 1]; ++j)
          price = std::min(price, slack[det_mech[j]]);
        if (!std::isfinite(price))
          continue;
        dual += price;
        for (int j = det_ptr[d]; j < det_ptr[d + 1]; ++j)
          slack[det_mech[j]] -= price;
      }
    if (best <= dual + 3.25 * min_pos_llr)
      return true;
    double alternative = HUGE_VAL;
    uint64_t other = 0;
    if (!repair(target, weight, alternative, other))
      return false;
    bool agree = other == mask;
    if (alternative < best) {
      best = alternative;
      mask = other;
    }
    return agree || best <= dual + 3.25 * min_pos_llr;
  }
  uint64_t hash_words(const uint64_t *w) const {
    uint64_t h = 0;
    for (int i = 0; i < syn_words; ++i) {
      uint64_t word = w[i];
      while (word) {
        h ^= detector_hash[i * 64 + __builtin_ctzll(word)];
        word &= word - 1;
      }
    }
    return h;
  }

  int lookup_single_mech(const uint64_t *syn) const {
    return lookup_hashed(syn, hash_words(syn));
  }

  int lookup_hashed(const uint64_t *syn, uint64_t h) const {
    uint64_t slot = h & ht_mask;
    for (size_t probe = 0; probe <= ht_mask; ++probe) {
      const auto &e = ht1[slot];
      if (e.mech_id < 0)
        return -1;
      if (e.key_hash == h) {
        const uint64_t *cb =
            &col_bits[static_cast<size_t>(e.mech_id) * syn_words];
        bool eq = true;
        for (int w = 0; w < syn_words; ++w) {
          if (cb[w] != syn[w]) {
            eq = false;
            break;
          }
        }
        if (eq)
          return e.mech_id;
      }
      slot = (slot + 1) & ht_mask;
    }
    return -1;
  }
};

} // namespace
extern "C" {
void *create_spacetime_decoder(int num_det, int num_mech, int num_obs,
                               const int32_t *det_indptr,
                               const int32_t *det_indices,
                               const float *llr_weights,
                               const uint64_t *obs_masks) {
  if (!qldpc::valid_columns(num_det, num_mech, num_obs, det_indptr, det_indices,
                            llr_weights, obs_masks))
    return nullptr;
  auto *dec = new FastSpaceTimeDecoder();
  dec->num_det = num_det;
  dec->num_mech = num_mech;
  dec->num_obs = num_obs;
  dec->syn_words = (num_det + 63) / 64;
  dec->llr.assign(llr_weights, llr_weights + num_mech);
  dec->llr_pos.resize(num_mech);
  dec->llr_bp.resize(num_mech);
  dec->obs_mask.assign(obs_masks, obs_masks + num_mech);
  dec->col_bits.assign(static_cast<size_t>(num_mech) * dec->syn_words, 0ULL);

  float min_l = 1e30f;
  for (int m = 0; m < num_mech; ++m) {
    float lp = llr_weights[m];
    dec->llr_pos[m] = lp;
    if (lp < min_l)
      min_l = lp;
    float tie =
        1.0f + 1e-4f *
                   static_cast<float>((static_cast<uint32_t>(m) * 2654435761U) &
                                      1023U) *
                   (1.0f / 1024.0f);
    dec->llr_bp[m] = llr_weights[m] * tie;
  }
  dec->min_pos_llr = (num_mech > 0) ? min_l : 1.0f;

  auto sorted = dec->llr_pos;
  std::sort(sorted.begin(), sorted.end());
  dec->pair_floor = num_mech >= 2 ? double(sorted[0]) + sorted[1] : HUGE_VAL;
  dec->triple_floor = num_mech >= 3 ? dec->pair_floor + sorted[2] : HUGE_VAL;
  dec->four_floor = num_mech >= 4 ? dec->triple_floor + sorted[3] : HUGE_VAL;
  dec->col_hash.resize(num_mech);
  dec->detector_hash.resize(num_det);
  for (int d = 0; d < num_det; ++d)
    dec->detector_hash[d] = splitmix64(d);
  dec->next_equal.assign(num_mech, -1);
  std::vector<std::vector<int>> det_adj(num_det);
  for (int m = 0; m < num_mech; ++m) {
    for (int k = det_indptr[m]; k < det_indptr[m + 1]; ++k) {
      int d = det_indices[k];
      dec->col_bits[static_cast<size_t>(m) * dec->syn_words + (d >> 6)] |=
          (1ULL << (d & 63));
      det_adj[d].push_back(m);
    }
  }
  int words = dec->syn_words;
  dec->cooccurrence.assign(size_t(num_det) * words, 0);
  for (int d = 0; d < num_det; ++d) {
    auto *covered = &dec->cooccurrence[size_t(d) * words];
    covered[d / 64] |= 1ULL << (d % 64);
    for (int id : det_adj[d])
      for (int w = 0; w < words; ++w)
        covered[w] |= dec->col_bits[size_t(id) * words + w];
  }
  dec->col_ptr.assign(det_indptr, det_indptr + num_mech + 1);
  dec->col_det.assign(det_indices, det_indices + det_indptr[num_mech]);
  dec->det_ptr.resize(num_det + 1, 0);
  for (int d = 0; d < num_det; ++d) {
    dec->det_ptr[d + 1] = dec->det_ptr[d] + static_cast<int>(det_adj[d].size());
    for (int m : det_adj[d])
      dec->det_mech.push_back(m);
  }

  size_t cap = 16;
  while (cap < static_cast<size_t>(num_mech) * 4)
    cap <<= 1;
  dec->ht_mask = cap - 1;
  dec->ht1.assign(cap, HashEntry1{});
  for (int m = 0; m < num_mech; ++m) {
    const uint64_t *cb =
        &dec->col_bits[static_cast<size_t>(m) * dec->syn_words];
    bool non_empty = false;
    for (int w = 0; w < dec->syn_words; ++w) {
      if (cb[w]) {
        non_empty = true;
        break;
      }
    }
    int weight = 0;
    for (int w = 0; w < dec->syn_words; ++w)
      weight += __builtin_popcountll(cb[w]);
    dec->max_col_weight = std::max(weight, dec->max_col_weight);
    if (!non_empty)
      continue;
    uint64_t h = dec->col_hash[m] = dec->hash_words(cb);
    uint64_t slot = h & dec->ht_mask;
    for (size_t pr = 0; pr < cap; ++pr) {
      auto &e = dec->ht1[slot];
      if (e.mech_id < 0) {
        e.key_hash = h;
        e.mech_id = m;
        break;
      }
      if (e.key_hash == h) {
        const uint64_t *eb =
            &dec->col_bits[static_cast<size_t>(e.mech_id) * dec->syn_words];
        bool eq = true;
        for (int w = 0; w < dec->syn_words; ++w) {
          if (eb[w] != cb[w]) {
            eq = false;
            break;
          }
        }
        if (eq) {
          if (dec->llr_pos[m] <= dec->llr_pos[e.mech_id]) {
            if (dec->llr_pos[m] == dec->llr_pos[e.mech_id])
              dec->next_equal[m] = e.mech_id;
            e.mech_id = m;
          }
          break;
        }
      }
      slot = (slot + 1) & dec->ht_mask;
    }
  }
  dec->prepare_overlap();
  dec->work.prepare(num_det, num_mech, dec->det_mech.size(), dec->syn_words);
  return dec;
}

void destroy_spacetime_decoder(void *ptr) {
  delete static_cast<FastSpaceTimeDecoder *>(ptr);
}

int decode_spacetime_batch(void *ptr, const uint8_t *syndromes_u8, int n_shots,
                           int n_bytes_per_shot, int bp_iters, float bp_alpha,
                           float bp_damping, uint8_t *out_obs_u8) {
  if (!ptr || n_shots < 0 || (n_shots && (!syndromes_u8 || !out_obs_u8)))
    return -1;

  auto *dec = static_cast<FastSpaceTimeDecoder *>(ptr);
  const int D = dec->num_det;
  const int M = dec->num_mech;
  const int W = dec->syn_words;
  const int CW = (D + 63) / 64;
  const int E = static_cast<int>(dec->det_mech.size());
  if (W > 32 || CW > 32 || D > 2048 || n_bytes_per_shot != (D + 7) / 8)
    return -2;

  auto &work = dec->work;
  auto &quick_work = work.quick;
  auto &post = work.post;
  auto &c2v = work.messages;
  auto &syn_bit = work.syndrome;
  auto &active_hard = work.hard;
  auto &order = work.order;
  auto &rank_score = work.scores;
  auto &basis_cols = work.basis;
  auto &basis_comb = work.combinations;
  const int *det_ptr = dec->det_ptr.data();
  const int *det_mech = dec->det_mech.data();

  auto write_obs = [&](uint8_t *out_row, uint64_t ox) {
    for (int b = 0; b < dec->num_obs; ++b) {
      out_row[b] = static_cast<uint8_t>((ox >> b) & 1ULL);
    }
  };

  for (int shot = 0; shot < n_shots; ++shot) {
    const uint8_t *s_row =
        syndromes_u8 + static_cast<size_t>(shot) * n_bytes_per_shot;
    uint64_t syn_words[32] = {0};
    uint64_t any_or = 0ULL;
    for (int byte_i = 0; byte_i < n_bytes_per_shot; ++byte_i) {
      int d_base = byte_i << 3;
      if (d_base >= D)
        break;
      uint8_t v = s_row[byte_i];
      if (d_base + 8 > D) {
        v &= static_cast<uint8_t>((1U << (D - d_base)) - 1U);
      }
      if (v) {
        syn_words[d_base >> 6] |= (static_cast<uint64_t>(v) << (d_base & 63));
        any_or |= static_cast<uint64_t>(v);
      }
    }

    uint8_t *out_row = out_obs_u8 + static_cast<size_t>(shot) * dec->num_obs;
    if (!any_or) {
      std::memset(out_row, 0, dec->num_obs);
      continue;
    }

    int syn_weight = 0;
    for (int w = 0; w < W; ++w)
      syn_weight += __builtin_popcountll(syn_words[w]);
    double best_fast_cost;
    uint64_t best_fast_obs;
    if (dec->low_weight(syn_words, syn_weight, best_fast_cost, best_fast_obs)) {
      write_obs(out_row, best_fast_obs);
      continue;
    }
    if (dec->quick_osd(syn_words, syn_weight, quick_work, best_fast_cost,
                       best_fast_obs) ||
        dec->peel(syn_words, syn_weight, best_fast_cost, best_fast_obs)) {
      write_obs(out_row, best_fast_obs);
      continue;
    }
    // Price the remaining syndrome and build a local check graph for BP.

    for (int d = 0; d < D; ++d) {
      syn_bit[d] = static_cast<uint8_t>((syn_words[d >> 6] >> (d & 63)) & 1ULL);
    }

    // Sum of nonnegative detector prices bounded by every incident
    // mechanism cost gives a lower bound for any compatible explanation.
    auto &slack = work.slack;
    std::copy(dec->llr_pos.begin(), dec->llr_pos.end(), slack.begin());
    double dual = 0;
    auto &hits = work.hits;
    hits.assign(M, 0);
    auto &local_columns = work.local;
    local_columns.clear();
    auto &fringe = work.fringe;
    fringe.assign(D, 0);
    for (int d = 0; d < D; ++d) {
      if (!syn_bit[d])
        continue;
      double price = 1e30;
      for (int e = det_ptr[d]; e < det_ptr[d + 1]; ++e) {
        int m = det_mech[e];
        if (++hits[m] == 1)
          local_columns.push_back(m);
        price = std::min(price, slack[m]);
      }
      if (price == 1e30)
        continue;
      dual += price;
      for (int e = det_ptr[d]; e < det_ptr[d + 1]; ++e)
        slack[det_mech[e]] -= price;
    }
    for (int m : local_columns) {
      int first = dec->col_ptr[m], last = dec->col_ptr[m + 1];
      if (2 * hits[m] < last - first)
        continue;
      for (int j = first; j < last; ++j)
        fringe[dec->col_det[j]] = 1;
    }
    // Include cheap short bridge columns in the supported neighborhood.
    for (int m = 0; m < M; ++m) {
      int first = dec->col_ptr[m], last = dec->col_ptr[m + 1];
      if (hits[m] || first == last || last - first > 2)
        continue;
      if (fringe[dec->col_det[first]] && fringe[dec->col_det[last - 1]])
        local_columns.push_back(m);
    }
    auto &ptr_local = work.ptr;
    ptr_local.assign(D + 1, 0);
    auto &edge_local = work.edges;
    for (int m : local_columns)
      for (int j = dec->col_ptr[m]; j < dec->col_ptr[m + 1]; ++j)
        ++ptr_local[1 + dec->col_det[j]];
    std::partial_sum(ptr_local.begin(), ptr_local.end(), ptr_local.begin());
    edge_local.resize(ptr_local.back());
    auto &cursor = work.cursor;
    cursor = ptr_local;
    for (int m : local_columns)
      for (int j = dec->col_ptr[m]; j < dec->col_ptr[m + 1]; ++j)
        edge_local[cursor[dec->col_det[j]]++] = m;

    double global_best_cost = best_fast_cost;
    uint64_t global_best_obs = best_fast_obs;
    for (int pass = 0; pass < 3; ++pass) {
      bool quick = (pass == 0);
      bool local = (pass < 2);
      bool compatible_osd = false;
      const int *det_ptr = local ? ptr_local.data() : dec->det_ptr.data();
      const int *det_mech = local ? edge_local.data() : dec->det_mech.data();
      int count = local ? int(local_columns.size()) : M;
      post = dec->llr_bp;
      c2v.assign(local ? edge_local.size() : E, 0.0f);

      bool converged = false;
      float best_bp_cost = 1e30f;
      uint64_t best_bp_obs = 0ULL;

      for (int it = 0; it < (quick ? 0 : std::min(bp_iters, local ? 3 : 5));
           ++it) {
        const bool rev = (it & 1) != 0;
        for (int step = 0; step < D; ++step) {
          const int d = rev ? (D - 1 - step) : step;
          const int p0 = det_ptr[d];
          const int p1 = det_ptr[d + 1];
          if (p0 == p1)
            continue;

          update_check(det_mech + p0, p1 - p0, syn_bit[d], post.data(),
                       c2v.data() + p0, work.extrinsic.data() + p0, bp_alpha,
                       bp_damping);
        }

        active_hard.clear();
        uint64_t acc[32] = {0};
        for (int j = 0; j < count; ++j) {
          int m = local ? local_columns[j] : j;
          if (post[m] < 0.0f) {
            active_hard.push_back(m);
            const uint64_t *cb = &dec->col_bits[static_cast<size_t>(m) * W];
            for (int w = 0; w < W; ++w)
              acc[w] ^= cb[w];
          }
        }
        bool ok = true;
        for (int w = 0; w < W; ++w) {
          if (acc[w] != syn_words[w]) {
            ok = false;
            break;
          }
        }
        if (ok) {
          // Greedy 2-to-1 triangle/duplicate contraction via O(1) hash table
          bool improved = true;
          while (improved && active_hard.size() >= 2 &&
                 active_hard.size() <= 16) {
            improved = false;
            for (size_t i = 0; i < active_hard.size() && !improved; ++i) {
              int m1 = active_hard[i];
              const uint64_t *cb1 = &dec->col_bits[static_cast<size_t>(m1) * W];
              for (size_t j = i + 1; j < active_hard.size(); ++j) {
                int m2 = active_hard[j];
                const uint64_t *cb2 =
                    &dec->col_bits[static_cast<size_t>(m2) * W];
                uint64_t xw[32];
                bool non_zero = false;
                for (int w = 0; w < W; ++w) {
                  xw[w] = cb1[w] ^ cb2[w];
                  if (xw[w])
                    non_zero = true;
                }
                if (!non_zero) {
                  active_hard.erase(active_hard.begin() +
                                    static_cast<ptrdiff_t>(j));
                  active_hard.erase(active_hard.begin() +
                                    static_cast<ptrdiff_t>(i));
                  improved = true;
                  break;
                }
                int m_alt = dec->lookup_single_mech(xw);
                if (m_alt >= 0 &&
                    dec->llr_pos[m_alt] < dec->llr_pos[m1] + dec->llr_pos[m2]) {
                  active_hard[i] = m_alt;
                  active_hard.erase(active_hard.begin() +
                                    static_cast<ptrdiff_t>(j));
                  improved = true;
                  break;
                }
              }
            }
          }
          float c = 0.0f;
          uint64_t ox = 0ULL;
          for (int m : active_hard) {
            c += dec->llr_pos[m];
            ox ^= dec->obs_mask[m];
          }
          converged = true;
          best_bp_cost = c;
          best_bp_obs = ox;
          break;
        }
      }

      if (converged && best_bp_cost < global_best_cost) {
        global_best_cost = best_bp_cost;
        global_best_obs = best_bp_obs;
      }

      auto run_active_conflict_osd = [&](const float *scores, int k_scan_cap,
                                         int k2_cap, int k3_cap) {
        if (local)
          std::copy(local_columns.begin(), local_columns.end(), order.begin());
        else
          std::iota(order.begin(), order.end(), 0);
        int top_sort = std::min(count, D + 200);
        auto less_reliable = [&](int a, int b) {
          if (scores[a] != scores[b])
            return scores[a] < scores[b];
          return a < b;
        };
        if (top_sort < count)
          std::nth_element(order.begin(), order.begin() + top_sort,
                           order.begin() + count, less_reliable);
        std::sort(order.begin(), order.begin() + top_sort, less_reliable);

        int pivot_slot[2048];
        for (int d = 0; d < D; ++d)
          pivot_slot[d] = -1;

        float slot_cost[2048];
        uint64_t slot_obs[2048];
        auto &nonpiv_mechs = work.nonpiv;
        nonpiv_mechs.clear();
        nonpiv_mechs.reserve(k_scan_cap);
        auto &np_delta = work.delta;
        np_delta.clear();
        np_delta.reserve(size_t(k_scan_cap) * CW);
        int num_pivs = 0;

        // Reduce the target as its missing pivots arrive. Once both the target
        // and the bounded nonpivot pool are complete, later rows cannot alter
        // them.
        uint64_t s_rem[32];
        uint64_t piv_sol[32] = {0};
        std::copy_n(syn_words, W, s_rem);
        auto reduce_syn = [&]() -> int {
          for (int w = 0; w < W; ++w) {
            while (s_rem[w]) {
              int b = __builtin_ctzll(s_rem[w]);
              int d = (w << 6) + b;
              int slot = pivot_slot[d];
              if (slot < 0)
                return d;
              const uint64_t *bv = &basis_cols[static_cast<size_t>(slot) * W];
              const uint64_t *bc = &basis_comb[static_cast<size_t>(slot) * CW];
              for (int ww = w; ww < W; ++ww)
                s_rem[ww] ^= bv[ww];
              for (int cw = 0; cw <= (slot >> 6); ++cw)
                piv_sol[cw] ^= bc[cw];
            }
          }
          return -1;
        };

        int needed = reduce_syn();
        auto try_insert_cols = [&](int start_i, int end_i) {
          for (int idx = start_i; idx < end_i; ++idx) {
            int m = order[idx];
            uint64_t vec[32];
            uint64_t comb[32] = {0};
            const uint64_t *src = &dec->col_bits[static_cast<size_t>(m) * W];
            for (int w = 0; w < W; ++w)
              vec[w] = src[w];

            int lead_bit = -1;
            for (int w = 0; w < W; ++w) {
              while (vec[w]) {
                int b = __builtin_ctzll(vec[w]);
                int d = (w << 6) + b;
                int slot = pivot_slot[d];
                if (slot >= 0) {
                  const uint64_t *bv =
                      &basis_cols[static_cast<size_t>(slot) * W];
                  const uint64_t *bc =
                      &basis_comb[static_cast<size_t>(slot) * CW];
                  for (int ww = w; ww < W; ++ww)
                    vec[ww] ^= bv[ww];
                  for (int cw = 0; cw <= (slot >> 6); ++cw)
                    comb[cw] ^= bc[cw];
                } else {
                  lead_bit = d;
                  break;
                }
              }
              if (lead_bit >= 0)
                break;
            }
            if (lead_bit >= 0) {
              int slot = num_pivs++;
              pivot_slot[lead_bit] = slot;

              slot_cost[slot] = dec->llr_pos[m];
              slot_obs[slot] = dec->obs_mask[m];
              comb[slot >> 6] |= (1ULL << (slot & 63));
              std::memcpy(&basis_cols[static_cast<size_t>(slot) * W], vec,
                          W * sizeof(uint64_t));
              std::memcpy(&basis_comb[static_cast<size_t>(slot) * CW], comb,
                          CW * sizeof(uint64_t));
              if (lead_bit == needed)
                needed = reduce_syn();
            } else if (static_cast<int>(nonpiv_mechs.size()) < k_scan_cap) {
              nonpiv_mechs.push_back(m);
              np_delta.insert(np_delta.end(), comb, comb + CW);
            }
            if (needed < 0 &&
                static_cast<int>(nonpiv_mechs.size()) >= k_scan_cap)
              break;
          }
        };

        try_insert_cols(0, top_sort);

        if (needed >= 0) {
          if (top_sort == count)
            return;
          std::sort(order.begin() + top_sort, order.begin() + count,
                    [&](int a, int b) {
                      if (scores[a] != scores[b])
                        return scores[a] < scores[b];
                      return a < b;
                    });
          try_insert_cols(top_sort, count);
          if (needed >= 0)
            return;
        }

        compatible_osd = true;
        auto eval_piv_cost = [&](const uint64_t *ps) -> float {
          float c = 0.0f;
          for (int cw = 0; cw < CW; ++cw) {
            uint64_t word = ps[cw];
            while (word) {
              int b = __builtin_ctzll(word);
              c += slot_cost[(cw << 6) + b];
              word &= (word - 1ULL);
            }
          }
          return c;
        };

        uint64_t best_piv[32];
        std::memcpy(best_piv, piv_sol, CW * sizeof(uint64_t));
        int best_np1 = -1, best_np2 = -1, best_np3 = -1;
        float local_best = eval_piv_cost(piv_sol);

        int K = static_cast<int>(nonpiv_mechs.size());
        if (K > 0) {

          auto &direct_pool = work.direct;
          direct_pool.clear();
          auto &other_pool = work.other;
          other_pool.clear();
          direct_pool.reserve(K);
          other_pool.reserve(K);
          uint64_t union_direct[32] = {0};

          for (int j = 0; j < K; ++j) {
            int m = nonpiv_mechs[j];
            const uint64_t *comb = np_delta.data() + size_t(j) * CW;
            bool hits_piv = false;
            for (int cw = 0; cw < CW; ++cw) {
              if (comb[cw] & piv_sol[cw]) {
                hits_piv = true;
                break;
              }
            }
            if (hits_piv) {
              direct_pool.push_back(j);
              for (int cw = 0; cw < CW; ++cw)
                union_direct[cw] |= comb[cw];
              uint64_t cand_piv[32];
              for (int cw = 0; cw < CW; ++cw)
                cand_piv[cw] = piv_sol[cw] ^ comb[cw];
              float c1 = dec->llr_pos[m] + eval_piv_cost(cand_piv);
              if (c1 < local_best) {
                local_best = c1;
                std::memcpy(best_piv, cand_piv, CW * sizeof(uint64_t));
                best_np1 = m;
                best_np2 = -1;
                best_np3 = -1;
              }
            } else {
              other_pool.push_back(j);
            }
          }

          auto &active_j = work.active;
          active_j = direct_pool;
          if (static_cast<int>(active_j.size()) < k2_cap) {
            for (int j : other_pool) {
              const uint64_t *dj = &np_delta[static_cast<size_t>(j) * CW];
              bool bridges = false;
              for (int cw = 0; cw < CW; ++cw) {
                if (dj[cw] & union_direct[cw]) {
                  bridges = true;
                  break;
                }
              }
              if (bridges) {
                active_j.push_back(j);
                if (static_cast<int>(active_j.size()) >= k2_cap)
                  break;
              }
            }
          }
          if (static_cast<int>(active_j.size()) > k2_cap)
            active_j.resize(k2_cap);

          int K2 = static_cast<int>(active_j.size());
          for (int a1 = 0; a1 < K2; ++a1) {
            int j1 = active_j[a1];
            int m1 = nonpiv_mechs[j1];
            float w1 = dec->llr_pos[m1];
            if (w1 >= local_best)
              continue;
            const uint64_t *d1 = &np_delta[static_cast<size_t>(j1) * CW];
            for (int a2 = a1 + 1; a2 < K2; ++a2) {
              int j2 = active_j[a2];
              int m2 = nonpiv_mechs[j2];
              float w12 = w1 + dec->llr_pos[m2];
              if (w12 >= local_best)
                continue;
              const uint64_t *d2 = &np_delta[static_cast<size_t>(j2) * CW];
              uint64_t cand_piv[32];
              for (int cw = 0; cw < CW; ++cw)
                cand_piv[cw] = piv_sol[cw] ^ d1[cw] ^ d2[cw];
              float c2 = w12 + eval_piv_cost(cand_piv);
              if (c2 < local_best) {
                local_best = c2;
                std::memcpy(best_piv, cand_piv, CW * sizeof(uint64_t));
                best_np1 = m1;
                best_np2 = m2;
                best_np3 = -1;
              }
            }
          }

          int K3 = std::min(static_cast<int>(direct_pool.size()), k3_cap);
          for (int a1 = 0; a1 < K3; ++a1) {
            int j1 = direct_pool[a1];
            int m1 = nonpiv_mechs[j1];
            float w1 = dec->llr_pos[m1];
            if (w1 >= local_best)
              continue;
            const uint64_t *d1 = &np_delta[static_cast<size_t>(j1) * CW];
            for (int a2 = a1 + 1; a2 < K3; ++a2) {
              int j2 = direct_pool[a2];
              int m2 = nonpiv_mechs[j2];
              float w12 = w1 + dec->llr_pos[m2];
              if (w12 >= local_best)
                continue;
              const uint64_t *d2 = &np_delta[static_cast<size_t>(j2) * CW];
              for (int a3 = a2 + 1; a3 < K3; ++a3) {
                int j3 = direct_pool[a3];
                int m3 = nonpiv_mechs[j3];
                float w123 = w12 + dec->llr_pos[m3];
                if (w123 >= local_best)
                  continue;
                const uint64_t *d3 = &np_delta[static_cast<size_t>(j3) * CW];
                uint64_t cand_piv[32];
                for (int cw = 0; cw < CW; ++cw)
                  cand_piv[cw] = piv_sol[cw] ^ d1[cw] ^ d2[cw] ^ d3[cw];
                float c3 = w123 + eval_piv_cost(cand_piv);
                if (c3 < local_best) {
                  local_best = c3;
                  std::memcpy(best_piv, cand_piv, CW * sizeof(uint64_t));
                  best_np1 = m1;
                  best_np2 = m2;
                  best_np3 = m3;
                }
              }
            }
          }
        }

        if (local_best < global_best_cost) {
          global_best_cost = local_best;
          uint64_t ox = 0ULL;
          for (int cw = 0; cw < CW; ++cw) {
            uint64_t word = best_piv[cw];
            while (word) {
              int b = __builtin_ctzll(word);
              ox ^= slot_obs[(cw << 6) + b];
              word &= (word - 1ULL);
            }
          }
          if (best_np1 >= 0)
            ox ^= dec->obs_mask[best_np1];
          if (best_np2 >= 0)
            ox ^= dec->obs_mask[best_np2];
          if (best_np3 >= 0)
            ox ^= dec->obs_mask[best_np3];
          global_best_obs = ox;
        }
      };

      if (quick) {
        for (int m : local_columns) {
          int degree = dec->col_ptr[m + 1] - dec->col_ptr[m];
          rank_score[m] =
              dec->llr_pos[m] / (1 + hits[m]) + 0.8f * (degree - hits[m]);
        }
        run_active_conflict_osd(rank_score.data(), 40, 12, 4);
        if (compatible_osd &&
            global_best_cost <= dual + 3.25 * dec->min_pos_llr)
          break;
        continue;
      }
      run_active_conflict_osd(post.data(), converged ? 32 : 84,
                              converged ? 12 : 24, converged ? 4 : 10);

      if (!local && global_best_cost > 3.65f * dec->min_pos_llr) {
        for (int i = 0; i < count; ++i) {
          int m = local ? local_columns[i] : i;
          const uint64_t *cb = &dec->col_bits[static_cast<size_t>(m) * W];
          bool touches_syn = false;
          for (int w = 0; w < W; ++w) {
            if (cb[w] & syn_words[w]) {
              touches_syn = true;
              break;
            }
          }
          rank_score[m] = 0.25f * post[m] + 0.75f * dec->llr[m] +
                          (touches_syn ? -1.25f : 0.0f);
        }
        run_active_conflict_osd(rank_score.data(), 56, 20, 8);
      }

      // A bounded cost gap is a fallback heuristic, not a minimum-LLR
      // certificate.
      if (global_best_cost <= dual + 3.0 * dec->min_pos_llr)
        break;
    }
    write_obs(out_row, global_best_obs);
  }
  return 0;
}

} // extern "C"
