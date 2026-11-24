#pragma once
#include <stdint.h>

// Group elements are 0..m-1, identity 0. mul is an m-by-m Cayley table.
// Six terms describe supports of size a and 6-a. Times list the twelve
// matching layers in block order A,B,B-transposed,A-transposed.
// Returns the hook proxy through cap (cap+1 if absent), or -1 if unresolved.
extern "C" int hook_distance(int m, const int32_t *mul, int a,
                             const int32_t *terms, const int32_t *times,
                             int depth, int cap, int target_k);
// Tests one CSS sector in isolation. order indexes the six neighbors of a
// check.
extern "C" int sector_distance(int m, const int32_t *mul, int wa,
                               const int32_t *terms, const int32_t *order,
                               int z, int cap);
// Return one witnessed cyclic (4,2) code. Return 0 on success, -1 if absent.
extern "C" int synthesize_cyclic42(int n, int k, int distance,
                                   int32_t *six_terms, int32_t *twelve_times);
