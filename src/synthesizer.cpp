#include "qldpc/synthesizer.h"
#include "bits.hpp"
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
int gf2_rref_256(int rows, int cols, const U256 *in_rows, U256 *out_rref,
                 int *out_pivs) {
  std::vector<U256> A(in_rows, in_rows + rows);
  int r = 0;
  for (int c = 0; c < cols && r < rows; ++c) {
    int piv = -1;
    for (int i = r; i < rows; ++i) {
      if (A[i].get_bit(c)) {
        piv = i;
        break;
      }
    }
    if (piv < 0)
      continue;
    if (piv != r)
      std::swap(A[r], A[piv]);
    if (out_pivs)
      out_pivs[r] = c;
    for (int i = 0; i < rows; ++i) {
      if (i != r && A[i].get_bit(c))
        A[i] ^= A[r];
    }
    ++r;
  }
  if (out_rref) {
    for (int i = 0; i < r; ++i)
      out_rref[i] = A[i];
  }
  return r;
}

struct SynLogKey {
  U128 s;
  U128 l;
  bool operator==(const SynLogKey &o) const { return s == o.s && l == o.l; }
  bool operator<(const SynLogKey &o) const {
    return (s != o.s) ? (s < o.s) : (l < o.l);
  }
};

struct PreppedCheckSide {
  int n = 0;
  int num_chk = 0;
  int rank_stab = 0;
  int num_non_stab = 0;
  std::vector<U256> H_opp;
  std::vector<U256> rref_stab;
  std::vector<int> piv_stab;
  std::vector<int> non_stab_cols;

  void init(int n_in, int m_opp, const U256 *opp_rows, int m_same,
            const U256 *same_rows) {
    n = n_in;
    if (m_opp > 128) {
      std::vector<U256> rref_opp(m_opp);
      std::vector<int> piv_opp(m_opp);
      int rk =
          gf2_rref_256(m_opp, n, opp_rows, rref_opp.data(), piv_opp.data());
      num_chk = rk;
      H_opp.assign(rref_opp.begin(), rref_opp.begin() + rk);
    } else {
      num_chk = m_opp;
      H_opp.assign(opp_rows, opp_rows + m_opp);
    }
    rref_stab.resize(m_same);
    piv_stab.resize(m_same);
    rank_stab =
        gf2_rref_256(m_same, n, same_rows, rref_stab.data(), piv_stab.data());
    rref_stab.resize(rank_stab);
    piv_stab.resize(rank_stab);

    std::vector<uint8_t> is_piv(n, 0);
    for (int c : piv_stab)
      is_piv[c] = 1;
    non_stab_cols.clear();
    for (int c = 0; c < n; ++c) {
      if (!is_piv[c])
        non_stab_cols.push_back(c);
    }
    num_non_stab = static_cast<int>(non_stab_cols.size());
  }

  SynLogKey project_fault(U256 e) const {
    U128 s;
    for (int r = 0; r < num_chk; ++r) {
      uint64_t p = (e.w[0] & H_opp[r].w[0]) ^ (e.w[1] & H_opp[r].w[1]) ^
                   (e.w[2] & H_opp[r].w[2]) ^ (e.w[3] & H_opp[r].w[3]);
      if (__builtin_parityll(p))
        s.set_bit(r);
    }
    for (int r = 0; r < rank_stab; ++r) {
      if (e.get_bit(piv_stab[r]))
        e ^= rref_stab[r];
    }
    U128 l;
    int lim = std::min(128, num_non_stab);
    for (int j = 0; j < lim; ++j) {
      if (e.get_bit(non_stab_cols[j]))
        l.set_bit(j);
    }
    return {s, l};
  }
};

struct FerrersTemplate {
  int wA;
  int wB;
  int T;
  int tA[4];
  int tB[4];
  int tBT[4];
  int tAT[4];
};

struct GatePair {
  int c;
  int t;
};

void build_2bga_schedule_steps(int m, const int *mul, const int *inv,
                               const FerrersTemplate &tpl, const int *a_ord,
                               const int *b_ord,
                               std::vector<std::vector<GatePair>> &steps) {
  int n = 2 * m;
  steps.assign(tpl.T, {});
  for (int t = 0; t < tpl.T; ++t)
    steps[t].reserve(2 * m);

  for (int r = 0; r < m; ++r) {
    for (int u = 0; u < tpl.wA; ++u) {
      int au = a_ord[u];
      int au_inv = inv[au];
      int qL = mul[r * m + au];
      int qR_z = mul[r * m + au_inv];
      steps[tpl.tA[u]].push_back({n + r, qL});
      steps[tpl.tAT[u]].push_back({m + qR_z, n + m + r});
    }
    for (int v = 0; v < tpl.wB; ++v) {
      int bv = b_ord[v];
      int bv_inv = inv[bv];
      int qR = mul[bv * m + r];
      int qL_z = mul[bv_inv * m + r];
      steps[tpl.tB[v]].push_back({n + r, m + qR});
      steps[tpl.tBT[v]].push_back({qL_z, n + m + r});
    }
  }
}

bool verify_schedule_disjoint_and_heisenberg(
    int n, int mx, int mz, const U256 *hx_rows, const U256 *hz_rows,
    const std::vector<std::vector<GatePair>> &steps) {
  int N_tot = n + mx + mz;
  std::vector<int> used(N_tot, -1);
  for (size_t st = 0; st < steps.size(); ++st) {
    for (const auto &g : steps[st]) {
      if (g.c < 0 || g.c >= N_tot || g.t < 0 || g.t >= N_tot || g.c == g.t)
        return false;
      if (used[g.c] == static_cast<int>(st) ||
          used[g.t] == static_cast<int>(st))
        return false;
      used[g.c] = static_cast<int>(st);
      used[g.t] = static_cast<int>(st);
    }
  }

  int words_tot = (N_tot + 63) / 64;
  std::vector<uint64_t> x_obs(static_cast<size_t>(mx) * words_tot, 0ULL);
  std::vector<uint64_t> z_obs(static_cast<size_t>(mz) * words_tot, 0ULL);
  for (int ix = 0; ix < mx; ++ix) {
    int q = n + ix;
    x_obs[static_cast<size_t>(ix) * words_tot + (q >> 6)] |= (1ULL << (q & 63));
  }
  for (int iz = 0; iz < mz; ++iz) {
    int q = n + mx + iz;
    z_obs[static_cast<size_t>(iz) * words_tot + (q >> 6)] |= (1ULL << (q & 63));
  }

  for (int st = static_cast<int>(steps.size()) - 1; st >= 0; --st) {
    for (const auto &g : steps[st]) {
      int cw = g.c >> 6, cb = g.c & 63;
      int tw = g.t >> 6, tb = g.t & 63;
      for (int ix = 0; ix < mx; ++ix) {
        uint64_t *row = &x_obs[static_cast<size_t>(ix) * words_tot];
        uint64_t bit = (row[cw] >> cb) & 1ULL;
        row[tw] ^= (bit << tb);
      }
      for (int iz = 0; iz < mz; ++iz) {
        uint64_t *row = &z_obs[static_cast<size_t>(iz) * words_tot];
        uint64_t bit = (row[tw] >> tb) & 1ULL;
        row[cw] ^= (bit << cb);
      }
    }
  }

  for (int ix = 0; ix < mx; ++ix) {
    const uint64_t *row = &x_obs[static_cast<size_t>(ix) * words_tot];
    for (int q = 0; q < n; ++q) {
      int got = static_cast<int>((row[q >> 6] >> (q & 63)) & 1ULL);
      if (got != hx_rows[ix].get_bit(q))
        return false;
    }
    for (int q = n + mx; q < N_tot; ++q) {
      if ((row[q >> 6] >> (q & 63)) & 1ULL)
        return false;
    }
  }
  for (int iz = 0; iz < mz; ++iz) {
    const uint64_t *row = &z_obs[static_cast<size_t>(iz) * words_tot];
    for (int q = 0; q < n; ++q) {
      int got = static_cast<int>((row[q >> 6] >> (q & 63)) & 1ULL);
      if (got != hz_rows[iz].get_bit(q))
        return false;
    }
    for (int q = n; q < n + mx; ++q) {
      if ((row[q >> 6] >> (q & 63)) & 1ULL)
        return false;
    }
  }
  return true;
}

void propagate_elementary_hooks_cpp(
    int n, int mx, int mz, const std::vector<std::vector<GatePair>> &steps,
    std::vector<U256> &out_fx, std::vector<U256> &out_fz) {
  int N_tot = n + mx + mz;
  std::vector<U256> F_X(N_tot), F_Z(N_tot);
  out_fx.clear();
  out_fz.clear();
  out_fx.reserve(n + steps.size() * 2 * n);
  out_fz.reserve(n + steps.size() * 2 * n);
  for (int q = 0; q < n; ++q) {
    F_X[q].set_bit(q);
    F_Z[q].set_bit(q);
    out_fx.push_back(F_X[q]);
    out_fz.push_back(F_Z[q]);
  }
  for (int st = static_cast<int>(steps.size()) - 1; st >= 0; --st) {
    for (const auto &g : steps[st]) {
      F_X[g.c] ^= F_X[g.t];
      F_Z[g.t] ^= F_Z[g.c];
    }
    for (const auto &g : steps[st]) {
      if (!F_X[g.c].is_zero())
        out_fx.push_back(F_X[g.c]);
      if (!F_X[g.t].is_zero())
        out_fx.push_back(F_X[g.t]);
      if (!F_Z[g.c].is_zero())
        out_fz.push_back(F_Z[g.c]);
      if (!F_Z[g.t].is_zero())
        out_fz.push_back(F_Z[g.t]);
    }
  }
  std::sort(out_fx.begin(), out_fx.end());
  out_fx.erase(std::unique(out_fx.begin(), out_fx.end()), out_fx.end());
  std::sort(out_fz.begin(), out_fz.end());
  out_fz.erase(std::unique(out_fz.begin(), out_fz.end()), out_fz.end());
}

void build_2bga_hx_hz(int m, const int *mul, const int *inv, int wA,
                      const int *a_terms, int wB, const int *b_terms,
                      std::vector<U256> &hx, std::vector<U256> &hz) {
  hx.assign(m, U256{});
  hz.assign(m, U256{});
  for (int r = 0; r < m; ++r) {
    for (int u = 0; u < wA; ++u) {
      int col_a = mul[r * m + a_terms[u]];
      hx[r].set_bit(col_a);
      int col_at = m + mul[r * m + inv[a_terms[u]]];
      hz[r].set_bit(col_at);
    }
    for (int v = 0; v < wB; ++v) {
      int col_b = m + mul[b_terms[v] * m + r];
      hx[r].set_bit(col_b);
      int col_bt = mul[inv[b_terms[v]] * m + r];
      hz[r].set_bit(col_bt);
    }
  }
}

// For an abelian table, simultaneous addition to both data blocks and both
// check blocks permutes every scheduled layer. It also permutes stabilizer
// rows, hence preserves both syndrome-zero and stabilizer membership.
struct HookSearch {
  std::vector<SynLogKey> keys;
  std::vector<int> roots, single, pair, next1, next2;
  std::vector<std::pair<int, int>> edges;
  std::vector<std::vector<int>> incident;
  std::vector<unsigned char> blocked;
  int max_weight = 0, work = 0;
  bool capped = false;
  int node_limit;
  HookSearch(const PreppedCheckSide &side, const std::vector<U256> &vectors,
             int m, const int *mul, bool translate, int limit)
      : incident(m), node_limit(limit) {
    std::map<SynLogKey, int> ids;
    std::vector<U256> representatives;
    for (auto e : vectors) {
      auto key = side.project_fault(e);
      if (key.s.is_zero() && key.l.is_zero())
        continue;
      if (!ids.emplace(key, int(keys.size())).second)
        continue;
      representatives.push_back(e);
      keys.push_back(key);
    }
    int count = keys.size();
    blocked.assign(count, 0);
    for (int i = 0; i < count; ++i) {
      if (blocked[i])
        continue;
      roots.push_back(i);
      if (!translate)
        continue;
      for (int t = 0; t < m; ++t) {
        U256 v;
        auto e = representatives[i];
        for (int q = 0; q < 2 * m; ++q)
          if (e.get_bit(q))
            v.set_bit((q / m) * m + mul[t * m + q % m]);
        auto it = ids.find(side.project_fault(v));
        if (it != ids.end())
          blocked[it->second] = 1;
      }
    }
    std::fill(blocked.begin(), blocked.end(), 0);
    int size = 16;
    while (size < count * 2)
      size *= 2;
    single.assign(size, -1);
    next1.resize(count);
    size = 16;
    while (size < count * (count - 1))
      size *= 2;
    pair.assign(size, -1);
    for (int i = 0; i < count; ++i) {
      auto s = keys[i].s.lo;
      int bucket = splitmix64(s) & (single.size() - 1);
      next1[i] = single[bucket];
      single[bucket] = i;
      max_weight = std::max(max_weight, __builtin_popcountll(s));
      while (s) {
        incident[__builtin_ctzll(s)].push_back(i);
        s &= s - 1;
      }
      for (int j = 0; j < i; ++j) {
        bucket = splitmix64(keys[i].s.lo ^ keys[j].s.lo) & (pair.size() - 1);
        next2.push_back(pair[bucket]);
        pair[bucket] = edges.size();
        edges.emplace_back(i, j);
      }
    }
  }
  bool visit(uint64_t s, U128 logical, int left) {
    if (++work > node_limit) {
      capped = true;
      return false;
    }
    if (__builtin_popcountll(s) > left * max_weight)
      return false;
    if (left == 0)
      return !s && !logical.is_zero();
    if (!s)
      return false; // A shorter closed subset would already have been tested.
    if (left == 1) {
      for (int i = single[splitmix64(s) & (single.size() - 1)]; i >= 0;
           i = next1[i])
        if (!blocked[i] && keys[i].s.lo == s && keys[i].l != logical)
          return true;
      return false;
    }
    if (left == 2) {
      for (int p = pair[splitmix64(s) & (pair.size() - 1)]; p >= 0;
           p = next2[p]) {
        auto [i, j] = edges[p];
        if (!blocked[i] && !blocked[j] && (keys[i].s.lo ^ keys[j].s.lo) == s &&
            (keys[i].l ^ keys[j].l) != logical)
          return true;
      }
      return false;
    }
    int best = __builtin_ctzll(s);
    for (uint64_t t = s; t; t &= t - 1) {
      int d = __builtin_ctzll(t);
      if (incident[d].size() < incident[best].size())
        best = d;
    }
    std::vector<int> marked;
    bool found = false;
    for (int i : incident[best]) {
      if (blocked[i])
        continue;
      blocked[i] = 1;
      marked.push_back(i);
      found = visit(s ^ keys[i].s.lo, logical ^ keys[i].l, left - 1);
      if (found || capped)
        break;
    }
    for (int i : marked)
      blocked[i] = 0;
    return found;
  }
  bool at_weight(int w) {
    work = 0;
    capped = false;
    for (int i : roots) {
      blocked[i] = 1;
      bool found = visit(keys[i].s.lo, keys[i].l, w - 1);
      blocked[i] = 0;
      if (found || capped)
        return found;
    }
    return false;
  }
};

bool inspect_group(int m, const int32_t *mul, std::vector<int> &inverse,
                   bool &abelian) {
  if (!mul)
    return false;
  abelian = true;
  for (int i = 0; i < m; ++i) {
    if (mul[i] != i || mul[i * m] != i)
      return false;
    std::array<bool, 128> seen{};
    for (int j = 0; j < m; ++j) {
      int v = mul[i * m + j];
      if (v < 0 || v >= m || seen[v])
        return false;
      seen[v] = true;
      if (v == 0)
        inverse[i] = j;
      abelian &= v == mul[j * m + i];
    }
  }
  for (int i = 0; i < m; ++i)
    for (int j = 0; j < m; ++j)
      for (int k = 0; k < m; ++k)
        if (mul[mul[i * m + j] * m + k] != mul[i * m + mul[j * m + k]])
          return false;
  return true;
}

bool valid_terms(const int32_t *terms, int m, int wa) {
  if (!terms)
    return false;
  for (int i = 0; i < 6; ++i) {
    if (terms[i] < 0 || terms[i] >= m)
      return false;
    for (int j = i < wa ? 0 : wa; j < i; ++j)
      if (terms[i] == terms[j])
        return false;
  }
  return true;
}

} // namespace

int hook_distance(int m, const int32_t *mul, int wa, const int32_t *terms,
                  const int32_t *times, int depth, int cap, int target_k) {
  if (m < 4 || m > 64 || (wa != 3 && wa != 4) || depth < 6 || depth > 12 ||
      !times || cap == 0 || cap < -8 || cap > 8)
    return -1;
  int wb = 6 - wa;
  std::vector<int> inv(m);
  bool abelian = true;
  if (!inspect_group(m, mul, inv, abelian) || !valid_terms(terms, m, wa))
    return -1;
  FerrersTemplate tpl{wa, wb, depth, {}, {}, {}, {}};
  for (int i = 0; i < 12; ++i)
    if (times[i] < 0 || times[i] >= depth)
      return -1;
  std::copy_n(times, wa, tpl.tA);
  std::copy_n(times + wa, wb, tpl.tB);
  std::copy_n(times + 6, wb, tpl.tBT);
  std::copy_n(times + 6 + wb, wa, tpl.tAT);
  std::vector<U256> hx, hz;
  build_2bga_hx_hz(m, mul, inv.data(), wa, terms, wb, terms + wa, hx, hz);
  int k = 2 * m - gf2_rref_256(m, 2 * m, hx.data(), nullptr, nullptr) -
          gf2_rref_256(m, 2 * m, hz.data(), nullptr, nullptr);
  if (k != target_k)
    return 0;
  std::vector<std::vector<GatePair>> steps;
  build_2bga_schedule_steps(m, mul, inv.data(), tpl, terms, terms + wa, steps);
  if (!verify_schedule_disjoint_and_heisenberg(2 * m, m, m, hx.data(),
                                               hz.data(), steps))
    return -1;
  PreppedCheckSide x, z;
  x.init(2 * m, m, hz.data(), m, hx.data());
  z.init(2 * m, m, hx.data(), m, hz.data());
  std::vector<U256> fx, fz;
  propagate_elementary_hooks_cpp(2 * m, m, m, steps, fx, fz);
  if (cap < 0) {
    fx.assign(2 * m, U256{});
    for (int i = 0; i < 2 * m; ++i)
      fx[i].set_bit(i);
    fz = fx;
    cap = -cap;
  }
  HookSearch xs(x, fx, m, mul, abelian, 2000000),
      zs(z, fz, m, mul, abelian, 2000000);
  for (int w = 1; w <= cap; ++w) {
    if (xs.at_weight(w) || zs.at_weight(w))
      return w;
    if (xs.capped || zs.capped)
      return -1;
  }
  return cap + 1;
}

int sector_distance(int m, const int32_t *mul, int wa, const int32_t *terms,
                    const int32_t *order, int z, int cap) {
  if (m < 4 || m > 64 || (wa != 3 && wa != 4) || cap < 1 || cap > 8)
    return -1;
  if (!order || (z != 0 && z != 1))
    return -1;
  std::array<bool, 6> present{};
  for (int i = 0; i < 6; ++i) {
    int t = order[i];
    if (t < 0 || t >= 6 || present[t])
      return -1;
    present[t] = true;
  }
  int wb = 6 - wa;
  std::vector<int> inv(m);
  bool abelian = true;
  if (!inspect_group(m, mul, inv, abelian) || !valid_terms(terms, m, wa))
    return -1;
  std::vector<U256> hx, hz;
  build_2bga_hx_hz(m, mul, inv.data(), wa, terms, wb, terms + wa, hx, hz);
  PreppedCheckSide side;
  side.init(2 * m, m, (z ? hx : hz).data(), m, (z ? hz : hx).data());
  std::vector<U256> faults(2 * m);
  for (int i = 0; i < 2 * m; ++i)
    faults[i].set_bit(i);
  for (int i = 0; i < m; ++i) {
    U256 suffix;
    for (int j = 5; j >= 0; --j) {
      int t = order[j];
      int q;
      if (!z)
        q = t < wa ? mul[i * m + terms[t]] : m + mul[terms[t] * m + i];
      else
        q = t < wb ? mul[inv[terms[wa + t]] * m + i]
                   : m + mul[i * m + inv[terms[t - wb]]];
      suffix.set_bit(q);
      faults.push_back(suffix);
    }
  }
  HookSearch search(side, faults, m, mul, abelian, 2000000);
  for (int w = 1; w <= cap; ++w) {
    if (search.at_weight(w))
      return w;
    if (search.capped)
      return -1;
  }
  return cap + 1;
}

#include "qldpc/code.hpp"
#include <stdexcept>

namespace qldpc {
Code build_code(const std::vector<int> &cayley, int m, int wa,
                const std::array<int, 6> &terms,
                const std::array<int, 12> &times) {
  if (m < 4 || m > 128 || int(cayley.size()) != m * m || (wa != 3 && wa != 4))
    throw std::invalid_argument("unsupported group dimensions");
  std::vector<int> inv(m);
  bool abelian;
  if (!inspect_group(m, cayley.data(), inv, abelian) ||
      !valid_terms(terms.data(), m, wa))
    throw std::invalid_argument("invalid group table or support");
  for (int t : times)
    if (t < 0 || t >= 12)
      throw std::invalid_argument("unsupported schedule depth");
  int depth = *std::max_element(times.begin(), times.end()) + 1;
  int wb = 6 - wa;
  FerrersTemplate tpl{wa, wb, depth, {}, {}, {}, {}};
  std::copy_n(times.begin(), wa, tpl.tA);
  std::copy_n(times.begin() + wa, wb, tpl.tB);
  std::copy_n(times.begin() + 6, wb, tpl.tBT);
  std::copy_n(times.begin() + 6 + wb, wa, tpl.tAT);
  std::vector<std::vector<GatePair>> steps;
  std::vector<U256> hx, hz;
  build_2bga_schedule_steps(m, cayley.data(), inv.data(), tpl, terms.data(),
                            terms.data() + wa, steps);
  build_2bga_hx_hz(m, cayley.data(), inv.data(), wa, terms.data(), wb,
                   terms.data() + wa, hx, hz);
  if (!verify_schedule_disjoint_and_heisenberg(2 * m, m, m, hx.data(),
                                               hz.data(), steps))
    throw std::invalid_argument("schedule fails stabilizer pullback");
  Code code{2 * m, {}, {}, {}};
  for (int i = 0; i < m; ++i) {
    code.hx.emplace_back(2 * m);
    code.hz.emplace_back(2 * m);
    for (int q = 0; q < 2 * m; ++q) {
      code.hx.back()[q] = hx[i].get_bit(q);
      code.hz.back()[q] = hz[i].get_bit(q);
    }
  }
  for (auto &tick : steps) {
    code.schedule.emplace_back();
    for (auto g : tick)
      code.schedule.back().emplace_back(g.c, g.t);
  }
  return code;
}
} // namespace qldpc

namespace {
constexpr int balanced_ticks[][12] = {{0, 2, 3, 5, 4, 1, 1, 4, 5, 3, 2, 0},
                                      {0, 1, 4, 5, 3, 2, 2, 3, 5, 4, 1, 0},
                                      {1, 2, 3, 4, 5, 0, 0, 5, 4, 3, 2, 1}};
bool canonical(std::array<int, 4> a, int m) {
  for (int origin : a) {
    auto translated = a;
    for (auto &i : translated)
      i = (i - origin + m) % m;
    std::sort(translated.begin(), translated.end());
    if (translated < a)
      return false;
  }
  return true;
}
int degree(uint64_t poly) { return poly ? 63 - __builtin_clzll(poly) : -1; }
uint64_t polynomial_gcd(uint64_t a, uint64_t b) {
  while (b) {
    while (degree(a) >= degree(b))
      a ^= b << (degree(a) - degree(b));
    std::swap(a, b);
  }
  return a;
}
std::vector<int> cyclic_table(int m) {
  std::vector<int> table(m * m);
  for (int i = 0; i < m; ++i)
    for (int j = 0; j < m; ++j)
      table[i * m + j] = (i + j) % m;
  return table;
}
} // namespace

int synthesize_cyclic42(int n, int k, int distance, int *terms, int *times) {
  if (!terms || !times || n < 8 || n > 128 || n % 2 || k <= 0 || k % 2 ||
      distance < 1 || distance > 8)
    return -1;
  int m = n / 2;
  auto mul = cyclic_table(m);
  for (int h = 1; h < m; ++h) {
    // Unit multiplication normalizes a binomial step to gcd(step,m).
    if (m % h || h < k / 2 || m / h < distance)
      continue;
    for (int i = 1; i < m; ++i)
      for (int j = i + 1; j < m; ++j)
        for (int l = j + 1; l < m; ++l) {
          uint64_t a = 1ULL | (1ULL << i) | (1ULL << j) | (1ULL << l);
          if (2 * degree(polynomial_gcd(a, 1ULL | (1ULL << h))) != k ||
              !canonical({0, i, j, l}, m))
            continue;
          int candidate[] = {0, i, j, l, 0, h};
          if (hook_distance(m, mul.data(), 4, candidate, balanced_ticks[0], 6,
                            -distance, k) != distance)
            continue;
          for (auto &t : balanced_ticks) {
            if (hook_distance(m, mul.data(), 4, candidate, t, 6, distance, k) !=
                distance)
              continue;
            std::copy_n(candidate, 6, terms);
            std::copy_n(t, 12, times);
            return 0;
          }
        }
  }
  return -1;
}

qldpc::Code qldpc::synthesize_cyclic(int n, int k, int distance) {
  std::array<int, 6> terms;
  std::array<int, 12> ticks;
  if (synthesize_cyclic42(n, k, distance, terms.data(), ticks.data()) != 0)
    throw std::runtime_error("no cyclic witness in the template search");
  return build_code(cyclic_table(n / 2), n / 2, 4, terms, ticks);
}
