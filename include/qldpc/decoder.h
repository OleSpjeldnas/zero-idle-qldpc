#pragma once
#include <stdint.h>

// Each mechanism column lists distinct detector indices at offsets [i,i+1).
// LLRs must be finite and positive. Decode packed little-endian syndromes
// into one byte per observable. Use a separate handle per concurrent caller.
extern "C" {
void *create_spacetime_decoder(int detectors, int mechanisms, int observables,
                               const int32_t *offsets, const int32_t *indices,
                               const float *llrs, const uint64_t *masks);
void destroy_spacetime_decoder(void *);
int decode_spacetime_batch(void *, const uint8_t *, int shots,
                           int bytes_per_shot, int iterations, float scale,
                           float damping, uint8_t *output);
void *create_bposd_decoder(int, int, int, const int32_t *, const int32_t *,
                           const float *, const uint64_t *);
void destroy_bposd_decoder(void *);
int decode_bposd_batch(void *, const uint8_t *, int, int, int, float, float,
                       int order, int pool, uint8_t *);
}
