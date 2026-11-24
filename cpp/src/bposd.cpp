#include "model_checks.hpp"
#include "qldpc/decoder.h"
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <numeric>
#include <vector>

namespace {

struct FastControlDecoder {
  int num_det;
  int num_mech;
  int num_obs;
  int syn_words;
  std::vector<float> llr;
  std::vector<uint64_t> obs_mask;
  std::vector<int> det_edge_ptr;
  std::vector<int> det_edge_idx;
  std::vector<int> mech_edge_ptr;
  std::vector<int> mech_edge_idx;
  std::vector<uint64_t> col_bits;
};

} // namespace

extern "C" {

void *create_bposd_decoder(int num_det, int num_mech, int num_obs,
                           const int32_t *det_indptr,
                           const int32_t *det_indices, const float *llr_weights,
                           const uint64_t *obs_masks) {
  if (!qldpc::valid_columns(num_det, num_mech, num_obs, det_indptr, det_indices,
                            llr_weights, obs_masks))
    return nullptr;
  auto *dec = new FastControlDecoder();
  dec->num_det = num_det;
  dec->num_mech = num_mech;
  dec->num_obs = num_obs;
  dec->syn_words = (num_det + 63) / 64;
  dec->llr.assign(llr_weights, llr_weights + num_mech);
  dec->obs_mask.assign(obs_masks, obs_masks + num_mech);
  dec->col_bits.assign(static_cast<size_t>(num_mech) * dec->syn_words, 0ULL);

  std::vector<std::vector<int>> det_to_e(num_det);
  std::vector<std::vector<int>> mech_to_e(num_mech);
  int e_id = 0;
  for (int m = 0; m < num_mech; ++m) {
    for (int k = det_indptr[m]; k < det_indptr[m + 1]; ++k) {
      int d = det_indices[k];
      dec->col_bits[static_cast<size_t>(m) * dec->syn_words + (d >> 6)] |=
          (1ULL << (d & 63));
      det_to_e[d].push_back(e_id);
      mech_to_e[m].push_back(e_id);
      ++e_id;
    }
  }
  dec->det_edge_ptr.resize(num_det + 1, 0);
  for (int d = 0; d < num_det; ++d) {
    dec->det_edge_ptr[d + 1] =
        dec->det_edge_ptr[d] + static_cast<int>(det_to_e[d].size());
    for (int eid : det_to_e[d])
      dec->det_edge_idx.push_back(eid);
  }
  dec->mech_edge_ptr.resize(num_mech + 1, 0);
  for (int m = 0; m < num_mech; ++m) {
    dec->mech_edge_ptr[m + 1] =
        dec->mech_edge_ptr[m] + static_cast<int>(mech_to_e[m].size());
    for (int eid : mech_to_e[m])
      dec->mech_edge_idx.push_back(eid);
  }
  return dec;
}

void destroy_bposd_decoder(void *ptr) {
  delete static_cast<FastControlDecoder *>(ptr);
}

int decode_bposd_batch(void *ptr, const uint8_t *syndromes_u8, int n_shots,
                       int n_bytes_per_shot, int bp_iters, float bp_alpha,
                       float bp_damping, int osd_order, int osd_top_k,
                       uint8_t *out_obs_u8) {
  if (!ptr || n_shots < 0 || (n_shots && (!syndromes_u8 || !out_obs_u8)))
    return -1;

  const auto *dec = static_cast<const FastControlDecoder *>(ptr);
  const int D = dec->num_det;
  const int M = dec->num_mech;
  const int W = dec->syn_words;
  const int CW = (D + 63) / 64;
  const int E = static_cast<int>(dec->det_edge_idx.size());
  if (W > 32 || CW > 32 || D > 2048 || n_bytes_per_shot != (D + 7) / 8)
    return -2;

  std::vector<float> v2c(E), c2v(E), post(M);
  std::vector<uint8_t> syn_bit(D);
  std::vector<int> active_hard;
  active_hard.reserve(64);
  std::vector<int> order(M);
  std::vector<uint64_t> basis_cols(static_cast<size_t>(D) * W, 0ULL);
  std::vector<uint64_t> basis_comb(static_cast<size_t>(D) * CW, 0ULL);

  for (int shot = 0; shot < n_shots; ++shot) {
    const uint8_t *s_row =
        syndromes_u8 + static_cast<size_t>(shot) * n_bytes_per_shot;
    uint64_t syn_words[32] = {0};
    bool any_syn = false;
    for (int d = 0; d < D; ++d) {
      uint8_t b = (s_row[d >> 3] >> (d & 7)) & 1U;
      syn_bit[d] = b;
      if (b) {
        syn_words[d >> 6] |= (1ULL << (d & 63));
        any_syn = true;
      }
    }
    uint8_t *out_row = out_obs_u8 + static_cast<size_t>(shot) * dec->num_obs;
    if (!any_syn) {
      std::memset(out_row, 0, dec->num_obs);
      continue;
    }

    for (int m = 0; m < M; ++m) {
      float l0 = dec->llr[m];
      for (int p = dec->mech_edge_ptr[m]; p < dec->mech_edge_ptr[m + 1]; ++p) {
        int eid = dec->mech_edge_idx[p];
        v2c[eid] = l0;
        c2v[eid] = 0.0f;
      }
    }

    bool converged = false;
    for (int it = 0; it < bp_iters; ++it) {
      for (int d = 0; d < D; ++d) {
        int p0 = dec->det_edge_ptr[d];
        int p1 = dec->det_edge_ptr[d + 1];
        if (p0 == p1)
          continue;
        int sgn_prod = syn_bit[d] ? -1 : 1;
        float min1 = 1e30f, min2 = 1e30f;
        int min1_eid = -1;
        for (int p = p0; p < p1; ++p) {
          int eid = dec->det_edge_idx[p];
          float v = v2c[eid];
          if (v < 0.0f)
            sgn_prod = -sgn_prod;
          float av = std::fabs(v);
          if (av < min1) {
            min2 = min1;
            min1 = av;
            min1_eid = eid;
          } else if (av < min2) {
            min2 = av;
          }
        }
        for (int p = p0; p < p1; ++p) {
          int eid = dec->det_edge_idx[p];
          int self_sgn = (v2c[eid] < 0.0f) ? -1 : 1;
          float mag = (eid == min1_eid) ? min2 : min1;
          c2v[eid] = bp_alpha * static_cast<float>(sgn_prod * self_sgn) * mag;
        }
      }

      active_hard.clear();
      for (int m = 0; m < M; ++m) {
        float sum = dec->llr[m];
        int p0 = dec->mech_edge_ptr[m];
        int p1 = dec->mech_edge_ptr[m + 1];
        for (int p = p0; p < p1; ++p)
          sum += c2v[dec->mech_edge_idx[p]];
        post[m] = sum;
        if (sum < 0.0f)
          active_hard.push_back(m);
        for (int p = p0; p < p1; ++p) {
          int eid = dec->mech_edge_idx[p];
          v2c[eid] =
              (1.0f - bp_damping) * v2c[eid] + bp_damping * (sum - c2v[eid]);
        }
      }

      uint64_t acc[32] = {0};
      for (int m : active_hard) {
        const uint64_t *cb = &dec->col_bits[static_cast<size_t>(m) * W];
        for (int w = 0; w < W; ++w)
          acc[w] ^= cb[w];
      }
      bool ok = true;
      for (int w = 0; w < W; ++w) {
        if (acc[w] != syn_words[w]) {
          ok = false;
          break;
        }
      }
      if (ok) {
        converged = true;
        break;
      }
    }

    if (!converged) {
      std::iota(order.begin(), order.end(), 0);
      int top_sort = std::min(M, D + 240);
      std::partial_sort(order.begin(), order.begin() + top_sort, order.end(),
                        [&](int a, int b) {
                          if (post[a] != post[b])
                            return post[a] < post[b];
                          return a < b;
                        });

      int pivot_slot[2048];
      for (int d = 0; d < D; ++d)
        pivot_slot[d] = -1;
      int piv_mech[2048];
      std::vector<int> nonpiv_mechs;
      nonpiv_mechs.reserve(32);
      int num_pivs = 0;

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
                const uint64_t *bv = &basis_cols[static_cast<size_t>(slot) * W];
                const uint64_t *bc =
                    &basis_comb[static_cast<size_t>(slot) * CW];
                for (int ww = w; ww < W; ++ww)
                  vec[ww] ^= bv[ww];
                for (int cw = 0; cw < CW; ++cw)
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
            piv_mech[slot] = m;
            comb[slot >> 6] |= (1ULL << (slot & 63));
            std::memcpy(&basis_cols[static_cast<size_t>(slot) * W], vec,
                        W * sizeof(uint64_t));
            std::memcpy(&basis_comb[static_cast<size_t>(slot) * CW], comb,
                        CW * sizeof(uint64_t));
          } else if (static_cast<int>(nonpiv_mechs.size()) < osd_top_k) {
            nonpiv_mechs.push_back(m);
          }
          if (num_pivs == D &&
              static_cast<int>(nonpiv_mechs.size()) >= osd_top_k)
            break;
        }
      };

      try_insert_cols(0, top_sort);

      uint64_t s_rem[32];
      uint64_t piv_sol[32] = {0};
      auto reduce_syn = [&]() -> bool {
        for (int w = 0; w < W; ++w)
          s_rem[w] = syn_words[w];
        std::memset(piv_sol, 0, sizeof(piv_sol));
        for (int w = 0; w < W; ++w) {
          while (s_rem[w]) {
            int b = __builtin_ctzll(s_rem[w]);
            int d = (w << 6) + b;
            int slot = pivot_slot[d];
            if (slot < 0)
              return false;
            const uint64_t *bv = &basis_cols[static_cast<size_t>(slot) * W];
            const uint64_t *bc = &basis_comb[static_cast<size_t>(slot) * CW];
            for (int ww = w; ww < W; ++ww)
              s_rem[ww] ^= bv[ww];
            for (int cw = 0; cw < CW; ++cw)
              piv_sol[cw] ^= bc[cw];
          }
        }
        return true;
      };

      if (!reduce_syn() && top_sort < M) {
        std::sort(order.begin() + top_sort, order.end(), [&](int a, int b) {
          if (post[a] != post[b])
            return post[a] < post[b];
          return a < b;
        });
        try_insert_cols(top_sort, M);
        reduce_syn();
      }

      auto eval_piv_cost = [&](const uint64_t *ps) -> float {
        float c = 0.0f;
        for (int cw = 0; cw < CW; ++cw) {
          uint64_t word = ps[cw];
          while (word) {
            int b = __builtin_ctzll(word);
            int slot = (cw << 6) + b;
            if (slot < num_pivs)
              c += std::max(0.01f, dec->llr[piv_mech[slot]]);
            word &= (word - 1ULL);
          }
        }
        return c;
      };

      uint64_t best_piv[32];
      std::memcpy(best_piv, piv_sol, CW * sizeof(uint64_t));
      int best_np1 = -1, best_np2 = -1;
      float best_cost = eval_piv_cost(piv_sol);

      if (osd_order >= 1 && !nonpiv_mechs.empty()) {
        int K = static_cast<int>(nonpiv_mechs.size());
        std::vector<uint64_t> np_delta(static_cast<size_t>(K) * CW, 0ULL);
        for (int j = 0; j < K; ++j) {
          int m = nonpiv_mechs[j];
          uint64_t vec[32];
          uint64_t comb[32] = {0};
          const uint64_t *src = &dec->col_bits[static_cast<size_t>(m) * W];
          for (int w = 0; w < W; ++w)
            vec[w] = src[w];
          for (int w = 0; w < W; ++w) {
            while (vec[w]) {
              int b = __builtin_ctzll(vec[w]);
              int d = (w << 6) + b;
              int slot = pivot_slot[d];
              if (slot >= 0) {
                const uint64_t *bv = &basis_cols[static_cast<size_t>(slot) * W];
                const uint64_t *bc =
                    &basis_comb[static_cast<size_t>(slot) * CW];
                for (int ww = w; ww < W; ++ww)
                  vec[ww] ^= bv[ww];
                for (int cw = 0; cw < CW; ++cw)
                  comb[cw] ^= bc[cw];
              } else {
                vec[w] &= (vec[w] - 1ULL);
              }
            }
          }
          std::memcpy(&np_delta[static_cast<size_t>(j) * CW], comb,
                      CW * sizeof(uint64_t));

          uint64_t cand_piv[32];
          for (int cw = 0; cw < CW; ++cw)
            cand_piv[cw] = piv_sol[cw] ^ comb[cw];
          float c1 = std::max(0.01f, dec->llr[m]) + eval_piv_cost(cand_piv);
          if (c1 < best_cost) {
            best_cost = c1;
            std::memcpy(best_piv, cand_piv, CW * sizeof(uint64_t));
            best_np1 = m;
            best_np2 = -1;
          }
        }
        if (osd_order >= 2) {
          int K2 = std::min(K, 16);
          for (int j1 = 0; j1 < K2; ++j1) {
            int m1 = nonpiv_mechs[j1];
            float w1 = std::max(0.01f, dec->llr[m1]);
            const uint64_t *d1 = &np_delta[static_cast<size_t>(j1) * CW];
            for (int j2 = j1 + 1; j2 < K2; ++j2) {
              int m2 = nonpiv_mechs[j2];
              float w2 = w1 + std::max(0.01f, dec->llr[m2]);
              if (w2 >= best_cost)
                continue;
              const uint64_t *d2 = &np_delta[static_cast<size_t>(j2) * CW];
              uint64_t cand_piv[32];
              for (int cw = 0; cw < CW; ++cw)
                cand_piv[cw] = piv_sol[cw] ^ d1[cw] ^ d2[cw];
              float c2 = w2 + eval_piv_cost(cand_piv);
              if (c2 < best_cost) {
                best_cost = c2;
                std::memcpy(best_piv, cand_piv, CW * sizeof(uint64_t));
                best_np1 = m1;
                best_np2 = m2;
              }
            }
          }
        }
      }

      active_hard.clear();
      for (int cw = 0; cw < CW; ++cw) {
        uint64_t word = best_piv[cw];
        while (word) {
          int b = __builtin_ctzll(word);
          int slot = (cw << 6) + b;
          if (slot < num_pivs)
            active_hard.push_back(piv_mech[slot]);
          word &= (word - 1ULL);
        }
      }
      if (best_np1 >= 0)
        active_hard.push_back(best_np1);
      if (best_np2 >= 0)
        active_hard.push_back(best_np2);
    }

    uint64_t obs_xor = 0ULL;
    for (int m : active_hard)
      obs_xor ^= dec->obs_mask[m];
    for (int b = 0; b < dec->num_obs; ++b) {
      out_row[b] = static_cast<uint8_t>((obs_xor >> b) & 1ULL);
    }
  }
  return 0;
}

} // extern "C"
